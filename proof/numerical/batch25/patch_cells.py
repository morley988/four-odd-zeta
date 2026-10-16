from pathlib import Path
import re,json,os
from fractions import Fraction as F
project=Path(os.environ.get('FOUR_VALUE_PROJECT','work/Four_Value_Lean_Round20')).resolve()
root=project/'lean'
batchdir=Path(__file__).resolve().parent
def rat(q):
 q=F(q);return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'
for k in [0,5669,49999]:
 p=root/(f'FourValueBatchCell{k}.lean' if k else 'FourValueBatchFirstCell.lean')
 s=p.read_text().replace('set_option maxHeartbeats 0','set_option maxHeartbeats 0\nset_option profiler true')
 for name in ['U','V','K']:
  pat=rf'def {name} \(j : Fin 45\) : ℝ := \(\((.*?) : ℚ\):ℝ\)'
  s=re.sub(pat,lambda m:f'def {name}q (j : Fin 45) : ℚ := {m[1]}\ndef {name} (j : Fin 45) : ℝ := ({name}q j:ℝ)',s)
 s=s.replace('norm_num [U,V,K]','norm_num [U,V,K,Uq,Vq,Kq]')
 for name,t,conj,up in [('u_left',F(k,10000),False,'U'),('u_right',F(k+1,10000),False,'U'),('v_left',F(k,10000),True,'V'),('v_right',F(k+1,10000),True,'V')]:
  start=s.index('theorem '+name);end=s.index('\ntheorem ',start+8)
  header=s[start:s.index(' := by',start)]
  lemma='conjugate_distance_checked' if conj else 'distance_checked'
  sign='+' if conj else '-'
  body=f''' := by
  have hc : ∀ j : Fin 45, 0 ≤ {up}q j ∧
      (zr ({rat(t)}:ℚ)-(centerq j).1)^2+(zi ({rat(t)}:ℚ){sign}(centerq j).2)^2 ≤ ({up}q j)^2 := by decide +kernel
  simpa only [Rat.cast_zero, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat, {up}] using ({lemma} ({rat(t)}:ℚ) ({up}q j) j (hc j).1 (hc j).2)
'''
  s=s[:start]+header+body+s[end:]
 for name in ['U','V']:
  start=s.index('theorem '+name.lower()+'_cutoff');end=s.index('\ntheorem ',start+8)
  header=s[start:s.index(' := by',start)]
  s=s[:start]+header+f''' := by
  have hc : ∀ j : Fin 45, (1/50:ℚ) ≤ {name}q j := by decide +kernel
  have h := Rat.cast_le (K:=ℝ) |>.mpr (hc j)
  norm_num at h
  exact h
'''+s[end:]
 start=s.index('theorem log_bound');end=s.index('theorem knot_bound',start)
 header=s[start:s.index(' := by',start)]
 s=s[:start]+header+f""" := by
  have hc : ∀ j : Fin 45, pairCheck (Uq j+17/5000000000) (Vq j+17/5000000000) (Kq j) = true := by decide +kernel
  have h := pair_checked (Uq j+17/5000000000) (Vq j+17/5000000000) (Kq j) (hc j)
  convert h using 1 <;> norm_num [U,V,K]

"""+s[end:]
 start=s.index('theorem knot_bound');end=s.index('\ndef certificate',start)
 G=F(json.load(open(batchdir/f'data{k}.json'))['G'])
 s=s[:start]+f'''theorem knot_bound (m : ℕ) (hm : m ≤ 41) : G+basisKnot m*(∑ j, basisKnotWeight m j*K j) ≤ Numerical.height m := by
  have h := knots_checked ({rat(G)}:ℚ) Kq (by decide +kernel) m hm
  convert h using 1 <;> norm_num [G,K]
'''+s[end:]
 if k:
  width=f'({rat(F(k+1,10000))}:ℝ)-({rat(F(k,10000))}:ℝ)=(1/10000:ℝ)'
  s=s.replace('\ndef certificate',f'\ntheorem cell_width : {width} := by norm_num\n\ndef certificate')
  s=s.replace('g_bound := by convert g_bound using 1 <;> norm_num','g_bound := by rw [cell_width]; exact g_bound').replace('log_bound := by intro j; convert log_bound j using 1 <;> norm_num','log_bound := by rw [cell_width]; exact log_bound')
 p.write_text(s)

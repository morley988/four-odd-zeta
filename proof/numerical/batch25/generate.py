from pathlib import Path
from fractions import Fraction as F
from math import isqrt
from collections import defaultdict
import sys
import os
import json,numpy as np
from flint import arb,ctx
ctx.prec=256
project=Path(os.environ.get('FOUR_VALUE_PROJECT','work/Four_Value_Lean_Round20')).resolve()
root=project/'lean'
batchdir=Path(__file__).resolve().parent
w=json.load(open(project/'numerical/replay/round7_basis_witness.json'));grid=np.load(project/'numerical/replay/round7_real_grid.npz')
a=list(map(F,w['a']));centers=[tuple(map(F,c))for c in w['centers']]
k=int(sys.argv[1]) if len(sys.argv)>1 else 0;y=F(k+1,10000);left=F(k,10000);curv=F(17,5000000000)
def rat(q):
 q=F(q);return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'
def re(q):return f'({rat(q)}:ℝ)'
def rq(q):return f'({rat(q)}:ℚ)'
logs={};atans={}
def bound(kind,q):
 q=F(q);d=logs if kind=='log' else atans
 if q not in d:
  x=arb(q.numerator)/q.denominator
  v=x.log() if kind=='log' else x.atan()
  z=int((v*10**18).floor().unique_fmpz());d[q]=(f'{kind}_{len(d):03d}',F(z-2,10**18),F(z+3,10**18))
 return d[q]
Lc=defaultdict(F);Ac=defaultdict(F);constant=F(0)
def addJ(u,c):
 global constant
 Lc[u*u+y*y]+=c*u/2;Ac[u/y]+=c*y;constant-=c*u
for aa in a[5:]:Lc[2*aa]+=2*aa;constant-=2*aa
Lc[F(33,100)]-=F(33,10);constant+=F(33,10)
c=1+F(3,5)*y
addJ(c+1,5);addJ(c-1,-5)
for aa in a:addJ(c+aa,-1);addJ(c-aa,1);Lc[(1+aa)/(1-aa)]+=F(3,50000)
piC=-2*y+F(19,20000)
for q in Lc:bound('log',q)
for q in Ac:bound('atan',q)
U=[];V=[];K=[]
def dist(t,xx,zz):
 zr=1+F(6,5)*t-F(16,25)*t*t;zi=2*t+F(6,5)*t*t
 sq=((zr-xx)**2+(zi-zz)**2)*10**20
 n=isqrt(sq.numerator//sq.denominator)
 if F(n*n)<sq:n+=1
 return F(n,10**10)
for j,(x,z) in enumerate(centers):
 u=max(dist(left,x,z),dist(y,x,z),F(1,50));v=max(dist(left,x,-z),dist(y,x,-z),F(1,50))
 U.append(u);V.append(v);K.append(F(int(grid['K'][j,k]),10**8));bound('log',u+curv);bound('log',v+curv)
G=F(int(grid['G'][k]),10**8)
head='import FourValueBatchTools\n\nnoncomputable section\nnamespace OddZeta.FourValue.Batch.Cell0\nopen OddZeta.FourValue.Transcendental\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
s=[head]
for kind,d in [('log',logs),('atan',atans)]:
 for q,(name,lo,hi) in d.items():
  if kind=='log' and q not in Lc:continue
  s.append(f'theorem {name} : {re(lo)} ≤ Real.{"log" if kind=="log" else "arctan"} {re(q)} ∧ Real.{"log" if kind=="log" else "arctan"} {re(q)} ≤ {re(hi)} := by\n  have h := {kind}_checked {rq(q)} {rq(lo)} {rq(hi)} (by decide +kernel)\n  norm_num at h ⊢\n  exact h\n')
s.append('end OddZeta.FourValue.Batch.Cell0\n');(root/f'FourValueBatchEnclosures{k if k else ""}.lean').write_text('\n'.join(s).replace('Batch.Cell0',f'Batch.Cell{k}'))
s=['import FourValueBatchEnclosures\n\nnoncomputable section\nnamespace OddZeta.FourValue.Batch.Cell0\nopen OddZeta.FourValue.Transcendental\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n']
for name,vs in [('U',U),('V',V),('K',K)]:
 s.append(f'def {name} (j : Fin 45) : ℝ := (([{", ".join(rq(q) for q in vs)}].getD j.val 0 : ℚ):ℝ)\n')
s.append(f'def G : ℝ := {re(G)}\n')
s.append(f'theorem g_bound : certificateG {re(y)}-2*Real.pi*{re(y)}+cellSlope*{re(y-left)} ≤ G := by\n  norm_num [G,certificateG,certificateJ,targetNormalizationEntropy,entropyTerm,targetFactorialEndpoints,targetAlpha,targetEndpointTuple,cellSlope,Fin.sum_univ_succ]\n  linarith only ['+', '.join([d[q][0]+('.2' if coeff>0 else '.1') for d,cs in [(logs,Lc),(atans,Ac)] for q,coeff in cs.items() if coeff]+['pi_machin_enclosure.2' if piC>0 else 'pi_machin_enclosure.1'])+']\n')
for name,t,conj,up in [('u_left',left,False,'U'),('u_right',y,False,'U'),('v_left',left,True,'V'),('v_right',y,True,'V')]:
 center='star (analyticCenter j)' if conj else 'analyticCenter j'
 s.append(f'theorem {name} (j : Fin 45) : ‖(normalizedContourPoint {re(t)})^2-{center}‖ ≤ {up} j := by\n  apply norm_le_of_squares\n  · fin_cases j <;> norm_num [{up}]\n  · fin_cases j <;> norm_num [{up},normalizedContourPoint,analyticCenter,Certificate.centers,pow_two,Complex.mul_re,Complex.mul_im]\n')
for name in ['U','V']:
 s.append(f'theorem {name.lower()}_cutoff (j : Fin 45) : (1/50:ℝ) ≤ {name} j := by\n  fin_cases j <;> norm_num [{name}]\n')
s.append(f'theorem log_bound (j : Fin 45) : Real.log (U j+(34/25)*{re(y-left)}^2/4)+Real.log (V j+(34/25)*{re(y-left)}^2/4) ≤ K j := by\n  fin_cases j')
for u,v in zip(U,V):s.append('  · norm_num [U,V,K]\n    linarith only ['+logs[u+curv][0]+'.2, '+logs[v+curv][0]+'.2]')
s.append('theorem knot_bound (m : ℕ) (hm : m ≤ 41) : G+basisKnot m*(∑ j, basisKnotWeight m j*K j) ≤ Numerical.height m := by\n  interval_cases m <;> norm_num [G,K,basisKnot,basisLimit,basisKnotWeight,certificateWeight,certificateWeightRow,Certificate.weightRows,Numerical.height,Certificate.knotBounds,Fin.sum_univ_succ]\n')
s.append(f'def certificate : CellCertificate {re(left)} {re(y)} where\n  width_pos := by norm_num\n  G := G\n  K := K\n  U := U\n  V := V\n  g_bound := by simpa using g_bound\n  u_left := u_left\n  u_right := u_right\n  v_left := v_left\n  v_right := v_right\n  u_cutoff := u_cutoff\n  v_cutoff := v_cutoff\n  log_bound := by simpa using log_bound\n  knot_bound := knot_bound\n')
s.append(f'theorem all_knots_on_first_cell (m : ℕ) (hm : m ≤ 41) (y : ℝ) (hy : 0 < y) (hy1 : y ≤ {re(y)}) :\n    certificateG y-2*Real.pi*y+basisKnot m*analyticBasisPotential (basisKnotWeight m) ((normalizedContourPoint y)^2) ≤ Numerical.height m :=\n  cell_certificate_sound certificate m hm y hy hy.le hy1\n\n#print axioms all_knots_on_first_cell\nend OddZeta.FourValue.Batch.Cell0\n')
out='\n'.join(s).replace('Batch.Cell0',f'Batch.Cell{k}')
if k:
 out=out.replace('import FourValueBatchEnclosures\n',f'import FourValueBatchEnclosures{k}\n').replace('all_knots_on_first_cell','all_knots_on_cell').replace('(hy : 0 < y) (hy1',f'(hy : 0 < y) (hyl : {re(left)} ≤ y) (hy1').replace('hy hy.le hy1','hy hyl hy1')
 out=out.replace('g_bound := by simpa using g_bound','g_bound := by convert g_bound using 1 <;> norm_num').replace('log_bound := by simpa using log_bound','log_bound := by intro j; convert log_bound j using 1 <;> norm_num')
(root/f'FourValueBatchCell{k}.lean' if k else root/'FourValueBatchFirstCell.lean').write_text(out)
(batchdir/f'data{k}.json').write_text(json.dumps({'cell':k,'logs':len(logs),'atans':len(atans),'G':str(G),'U':list(map(str,U)),'V':list(map(str,V)),'K':list(map(str,K))},indent=2)+'\n')
print({'logs':len(logs),'atans':len(atans),'G':str(G)})

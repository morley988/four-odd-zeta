from pathlib import Path
p=Path('work/Four_Value_Lean_Round20/lean')
s=(p/'FourValueExternalTranscendental.lean').read_text()
a=s[s.index('open Lean Elab Term in'):s.index('noncomputable def values')]
a=a.replace('TextTree','External.TextTree').replace('`OddZeta.FourValue.External','`OddZeta.FourValue.FullGrid').replace('valueBlock_','gridBlock_').replace('external_transcendental_table','external_grid_table').replace('external26','fullgrid27').replace('transcendental_values.txt','grid_arithmetic.txt').replace('6900022','2300000').replace('4096+58*count','18*count').replace('4096+58*(64*start)','18*(64*start)').replace('58*64','18*64')
s='import FourValueFullGridExpressions\n\nnamespace OddZeta.FourValue.FullGrid\n'+a+'''
noncomputable def gridValues : External.TextTree := external_grid_table
noncomputable def gridInt (row : ℕ) : ℤ :=
 let s := gridValues.get (row/64)
 let n : ℤ := External.digits s (18*(row%64)+1) 16
 if String.Pos.Raw.get! s ⟨18*(row%64)⟩ = '-' then -n else n
noncomputable def G (k : Fin 50000) : ℚ := (gridInt (46*k.val):ℚ)/100000000
noncomputable def K (k : Fin 50000) (j : Fin 45) : ℚ := (gridInt (46*k.val+1+j.val):ℚ)/100000000

def uRow (k : Fin 50000) (j : Fin 45) : ℕ := 22+114*k.val+24+2*j.val
def vRow (k : Fin 50000) (j : Fin 45) : ℕ := uRow k j+1
noncomputable def U (k : Fin 50000) (j : Fin 45) : ℚ := External.argument (uRow k j)-17/5000000000
noncomputable def V (k : Fin 50000) (j : Fin 45) : ℚ := External.argument (vRow k j)-17/5000000000
end OddZeta.FourValue.FullGrid
'''
(p/'FourValueFullGridData.lean').write_text(s)
s='''import FourValueFullGridData

/-! Five explicitly admitted finite RATIONAL calculation families.
Independent exact checking: numerical/fullgrid27/verify_grid.py.
No analytic inequalities or interpolation theorems are admitted here. -/
noncomputable section
namespace OddZeta.FourValue.FullGrid

/-- Finite rational row identities and valid row indices. -/
theorem expression_rows (k : Fin 50000) : (gExpr k).Valid := by
 sorry -- EXTERNAL_FINITE_RATIONAL_CERTIFICATION_V1

/-- Rational interval arithmetic, with the kernel-proved pi enclosure. -/
theorem expression_upper (k : Fin 50000) : (gExpr k).box.hi ≤ G k := by
 sorry -- EXTERNAL_FINITE_RATIONAL_CERTIFICATION_V1

/-- Six exact rational inequalities per center and cell. -/
theorem distances (k : Fin 50000) (j : Fin 45) :
 (1/50:ℚ) ≤ U k j ∧ (1/50:ℚ) ≤ V k j ∧
 (Batch.zr (left k)-(Batch.centerq j).1)^2+(Batch.zi (left k)-(Batch.centerq j).2)^2 ≤ (U k j)^2 ∧
 (Batch.zr (right k)-(Batch.centerq j).1)^2+(Batch.zi (right k)-(Batch.centerq j).2)^2 ≤ (U k j)^2 ∧
 (Batch.zr (left k)-(Batch.centerq j).1)^2+(Batch.zi (left k)+(Batch.centerq j).2)^2 ≤ (V k j)^2 ∧
 (Batch.zr (right k)-(Batch.centerq j).1)^2+(Batch.zi (right k)+(Batch.centerq j).2)^2 ≤ (V k j)^2 := by
 sorry -- EXTERNAL_FINITE_RATIONAL_CERTIFICATION_V1

/-- Sum of two stored rational logarithm upper endpoints. -/
theorem pair_upper (k : Fin 50000) (j : Fin 45) :
 External.upper (uRow k j)+External.upper (vRow k j) ≤ K k j := by
 sorry -- EXTERNAL_FINITE_RATIONAL_CERTIFICATION_V1

/-- All 42 weighted rational knot inequalities on all 50,000 cells. -/
theorem knot_arithmetic (k : Fin 50000) (m : Fin 42) :
 G k+Batch.knotq m*(∑ j, Batch.weightq m j*K k j) ≤ Batch.heightq m := by
 sorry -- EXTERNAL_FINITE_RATIONAL_CERTIFICATION_V1

end OddZeta.FourValue.FullGrid
'''
(p/'FourValueExternalArithmetic.lean').write_text(s)
f=p/'lakefile.toml';s=f.read_text().replace('roots = [','roots = ["FourValueFullGridData", "FourValueExternalArithmetic", "FourValueFullGrid", ');f.write_text(s)

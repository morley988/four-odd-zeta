import FourValueFullGridData

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

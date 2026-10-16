import Mathlib.Tactic

/-! Exact corner inequalities imply uniform floor enclosures on open residue boxes.
These are mathematical implications; no certificate or numeric assumption is admitted here. -/
namespace OddZeta.FourValue.RationalBoxes

theorem affine_rectangle_nonneg (A B C l h a b x y : ℚ)
 (hx : l≤x ∧ x≤h) (hy : a≤y ∧ y≤b)
 (h00 : 0≤A*l+B*a+C) (h01 : 0≤A*l+B*b+C)
 (h10 : 0≤A*h+B*a+C) (h11 : 0≤A*h+B*b+C) :
 0≤A*x+B*y+C := by
 by_cases hA : 0≤A <;> by_cases hB : 0≤B
 · nlinarith [mul_nonneg hA (sub_nonneg.mpr hx.1),mul_nonneg hB (sub_nonneg.mpr hy.1)]
 · nlinarith [mul_nonneg hA (sub_nonneg.mpr hx.1),mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hB) (sub_nonpos.mpr hy.2)]
 · nlinarith [mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hA) (sub_nonpos.mpr hx.2),mul_nonneg hB (sub_nonneg.mpr hy.1)]
 · nlinarith [mul_nonneg (neg_nonneg.mpr (le_of_not_ge hA)) (sub_nonneg.mpr hx.2),
     mul_nonneg (neg_nonneg.mpr (le_of_not_ge hB)) (sub_nonneg.mpr hy.2)]

theorem affine_rectangle_pos (A B C l h a b x y : ℚ)
 (hx : l≤x ∧ x≤h) (hy : a<y ∧ y<b) (hB : B≠0)
 (h00 : 0≤A*l+B*a+C) (h01 : 0≤A*l+B*b+C)
 (h10 : 0≤A*h+B*a+C) (h11 : 0≤A*h+B*b+C) :
 0<A*x+B*y+C := by
 rcases lt_or_gt_of_ne hB with hB | hB
 · have he := affine_rectangle_nonneg A B C l h a b x b hx ⟨hy.1.le.trans hy.2.le,le_rfl⟩ h00 h01 h10 h11
   nlinarith [mul_pos_of_neg_of_neg hB (sub_neg.mpr hy.2)]
 · have he := affine_rectangle_nonneg A B C l h a b x a hx ⟨le_rfl,hy.1.le.trans hy.2.le⟩ h00 h01 h10 h11
   nlinarith [mul_pos hB (sub_pos.mpr hy.1)]

/-- The strict upper floor inequality comes from the open y interval even when
one or more corner inequalities are equalities. -/
theorem floor_ratio_rectangle (v s l h a b u y : ℚ) (L H : ℤ)
 (hu : 0<u) (hx : l≤u ∧ u≤h) (hy : a<y ∧ y<b) (hs : s≠0)
 (lo00 : (L:ℚ)*l≤v+s*a) (lo01 : (L:ℚ)*l≤v+s*b)
 (lo10 : (L:ℚ)*h≤v+s*a) (lo11 : (L:ℚ)*h≤v+s*b)
 (hi00 : v+s*a≤(H+1:ℚ)*l) (hi01 : v+s*b≤(H+1:ℚ)*l)
 (hi10 : v+s*a≤(H+1:ℚ)*h) (hi11 : v+s*b≤(H+1:ℚ)*h) :
 L≤⌊(v+s*y)/u⌋ ∧ ⌊(v+s*y)/u⌋≤H := by
 have hlo := affine_rectangle_nonneg (-(L:ℚ)) s v l h a b u y hx ⟨hy.1.le,hy.2.le⟩
   (by linarith) (by linarith) (by linarith) (by linarith)
 have hhi := affine_rectangle_pos (H+1:ℚ) (-s) (-v) l h a b u y hx hy (neg_ne_zero.mpr hs)
   (by linarith) (by linarith) (by linarith) (by linarith)
 constructor
 · apply Int.le_floor.mpr
   apply (le_div_iff₀ hu).mpr
   linarith
 · apply Int.floor_le_iff.mpr
   apply (div_lt_iff₀ hu).mpr
   linarith

#print axioms floor_ratio_rectangle
end OddZeta.FourValue.RationalBoxes

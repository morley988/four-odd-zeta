import FourValueBatchFirstCell
import FourValueBatchCell5669
import FourValueBatchCell49999

noncomputable section
namespace OddZeta.FourValue.Batch
open OddZeta.FourValue.Transcendental

def certifiedCells : List ℕ := [0, 5669, 49999]

/-- Every selected actual grid cell satisfies all 42 knot bounds throughout
its positive-height interval, with no numerical certificate hypothesis. -/
theorem selected_cells_bound (k : ℕ) (hk : k ∈ certifiedCells)
    (m : ℕ) (hm : m ≤ 41) (y : ℝ) (hy : 0 < y)
    (hl : (k:ℝ)/10000 ≤ y) (hh : y ≤ ((k:ℝ)+1)/10000) :
    certificateG y-2*Real.pi*y+
      basisKnot m*analyticBasisPotential (basisKnotWeight m) ((normalizedContourPoint y)^2) ≤ Numerical.height m := by
  simp [certifiedCells] at hk
  rcases hk with rfl | rfl | rfl
  · exact Cell0.all_knots_on_first_cell m hm y hy (by norm_num at hh ⊢; exact hh)
  · exact Cell5669.all_knots_on_cell m hm y hy (by norm_num at hl ⊢; exact hl) (by norm_num at hh ⊢; exact hh)
  · exact Cell49999.all_knots_on_cell m hm y hy (by norm_num at hl ⊢; exact hl) (by norm_num at hh ⊢; exact hh)

end OddZeta.FourValue.Batch

import FourValue
import FourValueExternalTranscendental

set_option Elab.async false
noncomputable section
namespace OddZeta.FourValue.ExternalInterface
open OddZeta.FourValue.External

/-- Transfer an identified table row to the exact rational constants used by
an analytic proof. Matching the row to the desired constants is still proved. -/
theorem log_bound_of_row (i : Fin logCount) (q lo hi : ℚ)
    (hq : argument i = q) (hl : lower i = lo) (hu : upper i = hi) :
    (lo:ℝ) ≤ Real.log (q:ℝ) ∧ Real.log (q:ℝ) ≤ (hi:ℝ) := by
  simpa only [hq,hl,hu] using log_values i

theorem atan_bound_of_row (i : Fin atanCount) (q lo hi : ℚ)
    (hq : argument (logCount+i) = q) (hl : lower (logCount+i) = lo)
    (hu : upper (logCount+i) = hi) :
    (lo:ℝ) ≤ Real.arctan (q:ℝ) ∧ Real.arctan (q:ℝ) ≤ (hi:ℝ) := by
  simpa only [hq,hl,hu] using atan_values i

end OddZeta.FourValue.ExternalInterface

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! The last transcendental step in the real exponent, checked in Lean.
The integral input is the exact trapezoidal bound, whose pointwise
validity is still supplied by the separate analytic/certificate argument. -/
open scoped BigOperators
namespace OddZeta.FourValue.LogBound
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def logLower : ℚ := 2 * ∑ j ∈ Finset.range 20,
  (261/461 : ℚ)^(2*j+1) / (2*j+1)

theorem log_361_lower : (logLower : ℝ) ≤ Real.log (361/100) := by
  have h := Real.sum_range_le_log_div
    (x := (261/461 : ℝ)) (by norm_num) (by norm_num) 20
  norm_num only [show (1+(261/461:ℝ))/(1-261/461) = 361/100 by norm_num] at h
  have hc : (logLower : ℝ) = 2 * ∑ j ∈ Finset.range 20,
      (261/461 : ℝ)^(2*j+1) / (2*j+1) := by
    simp [logLower]
  rw [hc]
  linarith

theorem rational_final_bound :
    (-13277632257660676586509793 / 1024000000000000000000000 : ℚ) -
      2*(361/200)^2*logLower+3*(361/200)^2 ≤ -577853339/50000000 := by
  norm_num [logLower, Finset.sum_range_succ]

theorem real_exponent_upper :
    (-13277632257660676586509793 / 1024000000000000000000000 : ℝ) -
      2*(361/200)^2*Real.log (361/100)+3*(361/200)^2 ≤
      -577853339/50000000 := by
  have h := log_361_lower
  have hq :
    (-13277632257660676586509793 / 1024000000000000000000000 : ℝ) -
      2*(361/200)^2*(logLower:ℝ)+3*(361/200)^2 ≤
      -577853339/50000000 := by
    norm_num [logLower, Finset.sum_range_succ]
  nlinarith

#print axioms log_361_lower
#print axioms rational_final_bound
#print axioms real_exponent_upper
end OddZeta.FourValue.LogBound

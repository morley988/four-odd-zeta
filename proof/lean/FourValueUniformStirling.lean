import FourValueConcreteContourComplete
import Mathlib.Analysis.SpecialFunctions.Stirling

noncomputable section
namespace OddZeta.FourValue
open Real

def factorialLogRemainder (m : ℕ) : ℝ :=
  Real.log (Nat.factorial m:ℝ)-((m:ℝ)+1/2)*Real.log (m:ℝ)+(m:ℝ)

theorem factorialLogRemainder_stirlingSeq (m : ℕ) (hm : 1≤m) :
    factorialLogRemainder m=Real.log (Stirling.stirlingSeq m)+Real.log 2/2 := by
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast (show m≠0 by omega)
  have h := Stirling.log_stirlingSeq_formula m
  rw [Real.log_mul (by norm_num) hm0,Real.log_div hm0 (Real.exp_ne_zero 1),Real.log_exp] at h
  unfold factorialLogRemainder
  linarith

theorem factorialLogRemainder_bounds (m : ℕ) (hm : 1≤m) :
    (11/12:ℝ)≤factorialLogRemainder m ∧ factorialLogRemainder m≤1 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m≠0 by omega)
  have hl := Stirling.log_stirlingSeq_bounded_by_constant j
  have hu := Stirling.log_stirlingSeq'_antitone (show 0≤j by omega)
  change Real.log (Stirling.stirlingSeq (j+1))≤Real.log (Stirling.stirlingSeq 1) at hu
  rw [Stirling.stirlingSeq_one,Real.log_div (Real.exp_ne_zero 1) (by positivity),Real.log_exp,
    Real.log_sqrt (by norm_num)] at hu
  rw [factorialLogRemainder_stirlingSeq (j+1) (by omega)]
  constructor <;> linarith

theorem log_factorial_explicit_bounds (m : ℕ) (hm : 1≤m) :
    ((m:ℝ)+1/2)*Real.log (m:ℝ)-(m:ℝ)+11/12≤Real.log (Nat.factorial m:ℝ) ∧
    Real.log (Nat.factorial m:ℝ)≤((m:ℝ)+1/2)*Real.log (m:ℝ)-(m:ℝ)+1 := by
  have h := factorialLogRemainder_bounds m hm
  unfold factorialLogRemainder at h
  constructor <;> linarith [h.1,h.2]

theorem log_factorial_main_error (m : ℕ) :
    |Real.log (Nat.factorial m:ℝ)-((m:ℝ)*Real.log (m:ℝ)-(m:ℝ))|≤
      (1/2)*Real.log ((m:ℝ)+1)+1 := by
  by_cases hm : m=0
  · simp [hm]
  have hm1 : 1≤m := by omega
  have h := log_factorial_explicit_bounds m hm1
  have hlog : 0≤Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
  have hmono : Real.log (m:ℝ)≤Real.log ((m:ℝ)+1) :=
    Real.log_le_log (by exact_mod_cast (show 0<m by omega)) (by linarith)
  apply abs_le.mpr
  constructor <;> nlinarith [h.1,h.2,Real.log_nonneg (show 1≤(m:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) m])]
end OddZeta.FourValue

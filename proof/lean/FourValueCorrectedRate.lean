import FourValueCorrectedZeta
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The corrected two-adic denominator loss is o(n²).
The physical-coordinate checkpoint remains unchanged; this namespace supplies
the arithmetic statements for the analytic-coordinate matrix. -/

noncomputable section
namespace OddZeta.FourValue.Corrected
open Filter
open scoped Topology

/-- A real logarithmic majorant for the two-adic loss of the selected minor. -/
def twoAdicLossEnvelope (n : ℕ) (Q : ℕ) : ℝ :=
  182*(n:ℝ)*(40*Real.log (800*(n:ℝ))+(padicValNat 2 Q:ℝ)*Real.log 2)

theorem twoAdicLoss_le_envelope (n Q : ℕ) (hn : 1≤n) :
    (analyticMinorSize n:ℝ)*(40*(Nat.log 2 (800*n):ℝ)+(padicValNat 2 Q:ℝ))*Real.log 2 ≤
      twoAdicLossEnvelope n Q := by
  have hl : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlog : (Nat.log 2 (800*n):ℝ)*Real.log 2≤Real.log (800*(n:ℝ)) := by
    have h := Real.natLog_le_logb (800*n) 2
    rw [Real.logb] at h
    have hh := (le_div_iff₀ hl).mp h
    simpa using hh
  have hs : (analyticMinorSize n:ℝ)≤182*(n:ℝ) := by
    exact_mod_cast analyticMinorSize_linear_bound n hn
  have hv : 0≤40*(Nat.log 2 (800*n):ℝ)+(padicValNat 2 Q:ℝ) := by positivity
  calc
    _ ≤ (182*(n:ℝ))*(40*(Nat.log 2 (800*n):ℝ)+(padicValNat 2 Q:ℝ))*Real.log 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hv) hl.le
    _ ≤ twoAdicLossEnvelope n Q := by
      unfold twoAdicLossEnvelope
      have he : (40*(Nat.log 2 (800*n):ℝ)+(padicValNat 2 Q:ℝ))*Real.log 2 ≤
          40*Real.log (800*(n:ℝ))+(padicValNat 2 Q:ℝ)*Real.log 2 := by nlinarith
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he (by positivity : 0≤182*(n:ℝ))

theorem twoAdicLossEnvelope_normalized_tendsto_zero (Q : ℕ) :
    Tendsto (fun n : ℕ => twoAdicLossEnvelope n Q/(n:ℝ)^2) atTop (𝓝 0) := by
  have hlog := normalized_linear_log_tendsto_zero (182*40) 800 (by norm_num)
  have hlin : Tendsto (fun n : ℕ =>
      (182*(padicValNat 2 Q:ℝ)*Real.log 2)/(n:ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
      (182*(padicValNat 2 Q:ℝ)*Real.log 2)
    simpa [div_eq_mul_inv] using h
  convert hlog.add hlin using 1
  · ext n
    unfold twoAdicLossEnvelope
    by_cases hn : n=0
    · simp [hn]
    · have hn' : (n:ℝ)≠0 := by exact_mod_cast hn
      field_simp
  · simp

theorem twoAdicLoss_normalized_tendsto_zero (Q : ℕ) :
    Tendsto (fun n : ℕ =>
      ((analyticMinorSize n:ℝ)*(40*(Nat.log 2 (800*n):ℝ)+(padicValNat 2 Q:ℝ))*Real.log 2)/(n:ℝ)^2)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a:=fun n : ℕ => twoAdicLossEnvelope n Q/(n:ℝ)^2)
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right (twoAdicLoss_le_envelope n Q hn) (sq_nonneg _)
  · exact twoAdicLossEnvelope_normalized_tendsto_zero Q

end OddZeta.FourValue.Corrected

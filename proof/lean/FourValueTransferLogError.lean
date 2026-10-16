import FourValueTransferPolynomialBound

noncomputable section
namespace OddZeta.FourValue
open Filter
open scoped Topology

theorem scaled_log_nat_div_tendsto_zero (B : ℝ) (hB : 0<B) :
    Tendsto (fun n : ℕ => Real.log (B*(n:ℝ))/(n:ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1:ℝ)≠0)
  have hn : Tendsto (fun n : ℕ => B*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hB
  have hh := (hlog.comp hn).mul_const B
  simpa only [zero_mul] using hh.congr (fun n => by
    dsimp only [Function.comp_def]
    by_cases hn : n=0
    · simp [hn]
    · have hn' : (n:ℝ)≠0 := by exact_mod_cast hn
      field_simp)

theorem normalized_linear_log_tendsto_zero (A B : ℝ) (hB : 0<B) :
    Tendsto (fun n : ℕ => A*(n:ℝ)*Real.log (B*(n:ℝ))/(n:ℝ)^2) atTop (𝓝 0) := by
  have h := (scaled_log_nat_div_tendsto_zero B hB).const_mul A
  simpa only [mul_zero] using h.congr (fun n => by
    by_cases hn : n=0
    · simp [hn]
    · have hn' : (n:ℝ)≠0 := by exact_mod_cast hn
      field_simp)

theorem actualAnalyticTransferFactor_log_bound (n : ℕ) (hn : 1≤n) :
    0≤Real.log (actualAnalyticTransferFactor n) ∧
    Real.log (actualAnalyticTransferFactor n)≤3300*(n:ℝ)*Real.log (400*(n:ℝ)) := by
  have hpos : 0<actualAnalyticTransferFactor n := lt_of_lt_of_le (by norm_num) (actualAnalyticTransferFactor_ge_one n hn)
  refine ⟨Real.log_nonneg (actualAnalyticTransferFactor_ge_one n hn),?_⟩
  have h := Real.log_le_log hpos (actualAnalyticTransferFactor_polynomial_power n hn)
  simpa only [Real.log_pow,Nat.cast_mul,Nat.cast_ofNat] using h

theorem actualAnalyticTransferFactor_normalized_log_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (actualAnalyticTransferFactor n)/(n:ℝ)^2) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a:=fun n : ℕ => 3300*(n:ℝ)*Real.log (400*(n:ℝ))/(n:ℝ)^2)
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have h := actualAnalyticTransferFactor_log_bound n hn
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg h.1 (sq_nonneg _))]
    exact div_le_div_of_nonneg_right h.2 (sq_nonneg _)
  · exact normalized_linear_log_tendsto_zero 3300 400 (by norm_num)

theorem actualAnalyticTransferFactor_squared_normalized_log_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log ((actualAnalyticTransferFactor n)^2)/(n:ℝ)^2) atTop (𝓝 0) := by
  have h := actualAnalyticTransferFactor_normalized_log_tendsto_zero.const_mul 2
  simpa [Real.log_pow,mul_div_assoc] using h
end OddZeta.FourValue

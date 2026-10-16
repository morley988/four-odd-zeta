import FourValueUniformMinorBound
import FourValueTransferLogError

noncomputable section
namespace OddZeta.FourValue
open Filter
open scoped Topology

def analyticMinorSize (n : ℕ) : ℕ := targetHankelDegree n+1-4

def minorLogOverhead (n : ℕ) (L D : ℝ) : ℝ :=
  Real.log (Nat.factorial (analyticMinorSize n):ℝ)+
  (analyticMinorSize n:ℝ)*(Real.log (100*(n:ℝ))+Real.log D)-
  4*(100*(n:ℝ))*(L-24)+2*Real.log (actualAnalyticTransferFactor n)

theorem analyticMinorSize_linear_bound (n : ℕ) (hn : 1≤n) : analyticMinorSize n≤182*n := by
  have h := targetHankelSize_linear_bound n hn
  unfold analyticMinorSize
  omega

theorem minor_factorial_log_bounds (n : ℕ) (hn : 1≤n) :
    0≤Real.log (Nat.factorial (analyticMinorSize n):ℝ) ∧
    Real.log (Nat.factorial (analyticMinorSize n):ℝ)≤182*(n:ℝ)*Real.log (182*(n:ℝ)) := by
  have hfact : (Nat.factorial (analyticMinorSize n):ℝ)≤((182*n:ℕ):ℝ)^(182*n) := by
    exact_mod_cast (Nat.factorial_le (analyticMinorSize_linear_bound n hn)).trans (Nat.factorial_le_pow (182*n))
  have hlog := Real.log_le_log (show (0:ℝ)<Nat.factorial (analyticMinorSize n) by positivity) hfact
  constructor
  · exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos (analyticMinorSize n))))
  · simpa only [Real.log_pow,Nat.cast_mul,Nat.cast_ofNat] using hlog

theorem minor_factorial_normalized_log_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (Nat.factorial (analyticMinorSize n):ℝ)/(n:ℝ)^2) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a:=fun n : ℕ => 182*(n:ℝ)*Real.log (182*(n:ℝ))/(n:ℝ)^2)
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have h := minor_factorial_log_bounds n hn
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg h.1 (sq_nonneg _))]
    exact div_le_div_of_nonneg_right h.2 (sq_nonneg _)
  · exact normalized_linear_log_tendsto_zero 182 182 (by norm_num)

theorem minor_size_normalized_tendsto_zero :
    Tendsto (fun n : ℕ => (analyticMinorSize n:ℝ)/(n:ℝ)^2) atTop (𝓝 0) := by
  have hlin : Tendsto (fun n : ℕ => 182*(n:ℝ)/(n:ℝ)^2) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (182:ℝ)
    simpa only [mul_zero] using h.congr (fun n => by dsimp only [Function.comp_def]; by_cases hn : n=0; simp [hn]; field_simp)
  apply squeeze_zero_norm' (a:=fun n : ℕ => 182*(n:ℝ)/(n:ℝ)^2)
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast analyticMinorSize_linear_bound n hn
  · exact hlin

theorem minor_size_log_normalized_tendsto_zero :
    Tendsto (fun n : ℕ => (analyticMinorSize n:ℝ)*Real.log (100*(n:ℝ))/(n:ℝ)^2) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a:=fun n : ℕ => 182*(n:ℝ)*Real.log (100*(n:ℝ))/(n:ℝ)^2)
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hl : 0≤Real.log (100*(n:ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1≤100*n by omega))
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hl
    exact_mod_cast analyticMinorSize_linear_bound n hn
  · exact normalized_linear_log_tendsto_zero 182 100 (by norm_num)

theorem minorLogOverhead_normalized_tendsto_zero (L D : ℝ) :
    Tendsto (fun n : ℕ => minorLogOverhead n L D/(n:ℝ)^2) atTop (𝓝 0) := by
  have hlin : Tendsto (fun n : ℕ => 400*(n:ℝ)*(L-24)/(n:ℝ)^2) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (400*(L-24))
    simpa only [mul_zero] using h.congr (fun n => by dsimp only [Function.comp_def]; by_cases hn : n=0; simp [hn]; field_simp <;> ring)
  have h := ((minor_factorial_normalized_log_tendsto_zero.add minor_size_log_normalized_tendsto_zero).add
    (minor_size_normalized_tendsto_zero.mul_const (Real.log D))).sub hlin
  have h' := h.add (actualAnalyticTransferFactor_normalized_log_tendsto_zero.const_mul 2)
  convert h' using 1
  · ext n
    unfold minorLogOverhead
    ring
  · ring
end OddZeta.FourValue

import FourValuePrimeAsymptotic
import FourValueCorrectedRate

noncomputable section
namespace OddZeta.FourValue.Corrected
open Filter
open scoped Topology Chebyshev

theorem analyticMinorSize_ratio_limit :
 Tendsto (fun n : ℕ => (analyticMinorSize n:ℝ)/(n:ℝ)) atTop (𝓝 (361/2:ℝ)) := by
 have he : Tendsto (fun n : ℕ => (analyticMinorSize n:ℝ)/(n:ℝ)-361/2) atTop (𝓝 0) := by
   apply squeeze_zero_norm' (a:=fun n : ℕ => 4/(n:ℝ))
   · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
     have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
     have h1 := Nat.div_mul_le_self (361*n) 2
     have h2 := Nat.lt_div_mul_add (a:=361*n) (by norm_num : 0<2)
     have hd : 4≤targetHankelDegree n+1 := by unfold targetHankelDegree; omega
     have hk : analyticMinorSize n+4=targetHankelDegree n+1 := Nat.sub_add_cancel hd
     have hkR : (analyticMinorSize n:ℝ)+4=(targetHankelDegree n:ℝ)+1 := by exact_mod_cast hk
     have ha : (targetHankelDegree n:ℝ)*2≤361*(n:ℝ) := by exact_mod_cast h1
     have hb : 361*(n:ℝ)<(targetHankelDegree n:ℝ)*2+2 := by exact_mod_cast h2
     have hlo : -4≤(analyticMinorSize n:ℝ)-(361/2)*(n:ℝ) := by linarith
     have hhi : (analyticMinorSize n:ℝ)-(361/2)*(n:ℝ)≤4 := by linarith
     rw [Real.norm_eq_abs,show (analyticMinorSize n:ℝ)/(n:ℝ)-361/2=
       ((analyticMinorSize n:ℝ)-(361/2)*(n:ℝ))/(n:ℝ) by field_simp]
     rw [abs_div,abs_of_pos hnR]
     exact div_le_div_of_nonneg_right (abs_le.mpr ⟨hlo,hhi⟩) hnR.le
   · simpa [div_eq_mul_inv] using
       (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (4:ℝ)
 simpa using he.add_const (361/2:ℝ)

/-- A coarse bound on the omitted interval plus all higher prime powers has this rate. -/
def smallPrimeEnvelope (n : ℕ) : ℝ :=
 40*(analyticMinorSize n:ℝ)*(ψ (800*(n:ℝ))-θ (800*(n:ℝ))+θ ((n:ℝ)/20))

theorem smallPrimeEnvelope_limit :
 Tendsto (fun n : ℕ => smallPrimeEnvelope n/(100*(n:ℝ))^2) atTop (𝓝 (361/10000:ℝ)) := by
 have hp := (PrimeAsymptotic.higher_power_limit 800 (by norm_num)).comp tendsto_natCast_atTop_atTop
 have ht := (PrimeAsymptotic.theta_scaled_limit (1/20) (by norm_num)).comp tendsto_natCast_atTop_atTop
 have hh := (analyticMinorSize_ratio_limit.mul (hp.add ht)).const_mul (40/10000:ℝ)
 convert hh using 1
 · ext n
   simp only [Function.comp_def,smallPrimeEnvelope]
   rw [show (1/20:ℝ)*(n:ℝ)=(n:ℝ)/20 by ring]
   by_cases hn : n=0
   · simp [hn]
   · have hnR : (n:ℝ)≠0 := by exact_mod_cast hn
     field_simp
     <;> ring
 · norm_num

#print axioms analyticMinorSize_ratio_limit
#print axioms smallPrimeEnvelope_limit
end OddZeta.FourValue.Corrected

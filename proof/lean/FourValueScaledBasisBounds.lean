import FourValueBasisLogBounds

noncomputable section
namespace OddZeta.FourValue
open Polynomial

theorem concreteAnalyticBasis_exp_bound (i : ℕ) (w : Fin 45→ℝ)
    (hw : ∀ l,0≤w l) (hs : ∑ l,w l=1) (z : ℂ) :
    ‖(concreteAnalyticBasis i w).eval z‖≤Real.exp
      ((i:ℝ)/2*analyticBasisPotential w z+45*Real.log 4+45*Real.log 2500+
        90*Real.log (1+‖z‖)) := by
  by_cases hz : (concreteAnalyticBasis i w).eval z=0
  · simp only [hz,norm_zero]
    exact (Real.exp_pos _).le
  · exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr hz)).mp
      (concreteAnalyticBasis_log_bound i w hw hs z hz)

theorem scaledAnalyticBasis_exp_bound (M : ℝ) (hM : 0<M) (i : ℕ) (w : Fin 45→ℝ)
    (hw : ∀ l,0≤w l) (hs : ∑ l,w l=1) (Z : ℂ) :
    ‖(scaledAnalyticBasis M i w).eval ((M:ℂ)^2*Z)‖≤
      M^(2*i)/(Nat.factorial (2*i):ℝ)*Real.exp
      ((i:ℝ)/2*analyticBasisPotential w Z+45*Real.log 4+45*Real.log 2500+
        90*Real.log (1+‖Z‖)) := by
  rw [scaledAnalyticBasis_norm M hM]
  exact mul_le_mul_of_nonneg_left (concreteAnalyticBasis_exp_bound i w hw hs Z) (by positivity)

theorem scaledAnalyticBasis_log_bound (M : ℝ) (hM : 0<M) (i : ℕ) (w : Fin 45→ℝ)
    (hw : ∀ l,0≤w l) (hs : ∑ l,w l=1) (Z : ℂ)
    (hZ : (scaledAnalyticBasis M i w).eval ((M:ℂ)^2*Z)≠0) :
    2*Real.log ‖(scaledAnalyticBasis M i w).eval ((M:ℂ)^2*Z)‖≤
      4*(i:ℝ)*Real.log M-2*Real.log (Nat.factorial (2*i):ℝ)+
      (i:ℝ)*analyticBasisPotential w Z+90*Real.log 4+90*Real.log 2500+
        180*Real.log (1+‖Z‖) := by
  have hz : (concreteAnalyticBasis i w).eval Z≠0 := by
    intro hz
    apply hZ
    rw [scaledAnalyticBasis_eval M hM.ne',hz,mul_zero]
  have hb := concreteAnalyticBasis_log_bound i w hw hs Z hz
  have hf : (Nat.factorial (2*i):ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [scaledAnalyticBasis_norm M hM,Real.log_mul (div_ne_zero (pow_ne_zero _ hM.ne') hf)
    (norm_ne_zero_iff.mpr hz),Real.log_div (pow_ne_zero _ hM.ne') hf,Real.log_pow]
  push_cast
  linarith

theorem scaledAnalyticBasis_natDegree (M : ℝ) (hM : M≠0) (i : ℕ) (w : Fin 45→ℝ)
    (hw : ∀ l,0≤w l) (hs : ∑ l,w l=1) : (scaledAnalyticBasis M i w).natDegree=i := by
  have hMc : (M:ℂ)≠0 := by exact_mod_cast hM
  have hf : (Nat.factorial (2*i):ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [scaledAnalyticBasis,natDegree_C_mul (div_ne_zero (pow_ne_zero _ hMc) hf),natDegree_comp,
    concreteAnalyticBasis_natDegree i w hw hs,natDegree_C_mul_X _ (inv_ne_zero (pow_ne_zero _ hMc)),mul_one]

theorem scaledAnalyticBasis_leadingCoeff (M : ℝ) (hM : M≠0) (i : ℕ) (w : Fin 45→ℝ)
    (hw : ∀ l,0≤w l) (hs : ∑ l,w l=1) :
    (scaledAnalyticBasis M i w).leadingCoeff=1/(Nat.factorial (2*i):ℂ) := by
  have hMc : (M:ℂ)≠0 := by exact_mod_cast hM
  have hd : (C ((M:ℂ)^2)⁻¹*X).natDegree≠0 := by
    rw [natDegree_C_mul_X _ (inv_ne_zero (pow_ne_zero _ hMc))]
    decide
  rw [scaledAnalyticBasis,leadingCoeff_mul,leadingCoeff_C,leadingCoeff_comp hd,
    (concreteAnalyticBasis_monic i w).leadingCoeff,leadingCoeff_C_mul_X,
    concreteAnalyticBasis_natDegree i w hw hs,one_mul,inv_pow,← pow_mul]
  field_simp

/-- The physical normalization is monic before division by (2i)!. -/
theorem scaledAnalyticBasis_factorial_monic (M : ℝ) (hM : M≠0) (i : ℕ)
    (w : Fin 45→ℝ) (hw : ∀ l,0≤w l) (hs : ∑ l,w l=1) :
    (C (Nat.factorial (2*i):ℂ)*scaledAnalyticBasis M i w).Monic := by
  unfold Monic
  rw [leadingCoeff_mul,leadingCoeff_C,scaledAnalyticBasis_leadingCoeff M hM i w hw hs]
  exact mul_one_div_cancel (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
end OddZeta.FourValue

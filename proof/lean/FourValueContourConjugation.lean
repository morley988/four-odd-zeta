import FourValueUniformDensity

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory

theorem analyticBlock_eval_star (c z : ℂ) (δ : ℝ) (m : ℕ) :
    (analyticBlock c δ m).eval (star z)=star ((analyticBlock (star c) δ m).eval z) := by
  by_cases hm : m=0 <;> simp [analyticBlock,hm]

theorem analyticBlockPair_eval_star (c z : ℂ) (δ : ℝ) (m : ℕ) :
    (analyticBlockPair c δ m).eval (star z)=star ((analyticBlockPair c δ m).eval z) := by
  simp only [analyticBlockPair,eval_mul,analyticBlock_eval_star,star_star,star_mul']
  ring

theorem concreteAnalyticBasis_eval_star (i : ℕ) (w : Fin 45→ℝ) (z : ℂ) :
    (concreteAnalyticBasis i w).eval (star z)=star ((concreteAnalyticBasis i w).eval z) := by
  simp only [concreteAnalyticBasis,roundedAnalyticBasis,analyticBasisPolynomial,eval_mul,eval_pow,eval_sub,eval_X,eval_C,eval_prod,analyticBlockPair_eval_star]
  simp

theorem scaledAnalyticBasis_eval_star (M : ℝ) (i : ℕ) (w : Fin 45→ℝ) (z : ℂ) :
    (scaledAnalyticBasis M i w).eval (star z)=star ((scaledAnalyticBasis M i w).eval z) := by
  simp only [scaledAnalyticBasis,eval_mul,eval_C,eval_comp,eval_X]
  have he : ((M:ℂ)^2)⁻¹*star z=star (((M:ℂ)^2)⁻¹*z) := by simp
  rw [he,concreteAnalyticBasis_eval_star]
  simp

theorem centeredDenominator_eval_star (a : ℕ) (z : ℂ) :
    (centeredDenominator (K:=ℂ) a).eval (star z)=star ((centeredDenominator (K:=ℂ) a).eval z) := by
  rw [centeredDenominator_integerProduct]
  simp [integerRootProduct,eval_prod]

theorem analyticWeight_star (n : ℕ) (z : ℂ) :
    analyticZetaFunction n 1 (star z)=star (analyticZetaFunction n 1 z) := by
  simp only [analyticZetaFunction_formula,eval_one,mul_one,centeredDenominator_eval_star]
  simp [targetNormalization]

theorem contourKernel_star (z : ℂ) (hz : 0<z.im) :
    contourKernel (star z)=star (contourKernel z) := by
  rw [contourKernel_integer_series_lower (star z) (by simpa using neg_neg_of_pos hz),
    contourKernel_integer_series z hz]
  rw [tsum_star]
  congr 1
  funext j
  simp

theorem lowerContourRay_eq_star (n : ℕ) (t : ℝ) : lowerContourRay n t=star (upperContourRay n t) := by
  simp [lowerContourRay,upperContourRay,baseContourRay]
  ring

theorem actualContourDensity_lower_eq_upper (n i : ℕ) (t : ℝ) (ht : 0<t) :
    ‖(actualAdaptedBasis n i).eval ((lowerContourRay n t)^2)‖^2*
      ‖analyticContourWeight n (lowerContourRay n t)‖=contourDensity n i t := by
  rw [lowerContourRay_eq_star,← star_pow]
  unfold actualAdaptedBasis
  rw [scaledAnalyticBasis_eval_star,norm_star]
  unfold analyticContourWeight
  rw [analyticWeight_star,contourKernel_star _ (by simpa [upperContourRay,baseContourRay] using ht),← star_mul',norm_star]
  rfl

theorem actualContourEnergy_lower_eq_upper (n i : ℕ) :
    contourRayEnergy n (actualAdaptedBasis n i) (lowerContourRay n)=
      contourRayEnergy n (actualAdaptedBasis n i) (upperContourRay n) := by
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact actualContourDensity_lower_eq_upper n i t ht
end OddZeta.FourValue

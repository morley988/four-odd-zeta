import FourValueUniformLaplace
import FourValueContourConjugation

noncomputable section
namespace OddZeta.FourValue

theorem actualContourSize_squared_energy (n i : ℕ) :
    (analyticContourSize n (actualAdaptedBasis n i))^2=
      2*contourNormalization*contourRayEnergy n (actualAdaptedBasis n i) (upperContourRay n) := by
  unfold analyticContourSize
  rw [actualContourEnergy_lower_eq_upper,mul_pow,Real.sq_sqrt contourNormalization_nonneg,
    Real.sq_sqrt (add_nonneg (contourRayEnergy_nonneg _ _ _) (contourRayEnergy_nonneg _ _ _))]
  ring

theorem actualContourSize_uniform_bound (L : ℝ) : ∃ D : ℝ,1≤D ∧
    ∀ n i : ℕ,1≤n → i≤targetHankelDegree n → ∀ V : ℝ,L≤V →
      (∀ y : ℝ,0<y → contourRate (adaptedIndexMass n i) y≤V) →
      analyticContourSize n (actualAdaptedBasis n i)≤
        Real.exp (((100*(n:ℝ))*(V+factorialRowRate (adaptedIndexMass n i))+
          Real.log (100*(n:ℝ))+Real.log D)/2) := by
  obtain ⟨C,hC,henergy⟩ := actualContourEnergy_uniform_laplace L
  let D := 2*contourNormalization*C+1
  have hD : 1≤D := by dsimp [D]; nlinarith [contourNormalization_nonneg]
  refine ⟨D,hD,?_⟩
  intro n i hn hi V hV hcert
  have he := henergy n i hn hi V hV hcert
  let a := analyticContourSize n (actualAdaptedBasis n i)
  let M : ℝ := 100*(n:ℝ)
  let R := V+factorialRowRate (adaptedIndexMass n i)
  have hM : 0<M := by dsimp [M]; exact_mod_cast (show 0<100*n by omega)
  have hD0 : 0<D := by linarith
  have hs : a^2≤D*M*Real.exp (M*R) := by
    rw [show a^2=2*contourNormalization*contourRayEnergy n (actualAdaptedBasis n i) (upperContourRay n) from actualContourSize_squared_energy n i]
    calc
      _ ≤ 2*contourNormalization*(M*C*Real.exp (M*R)) :=
        mul_le_mul_of_nonneg_left he (by positivity [contourNormalization_nonneg])
      _ ≤ D*M*Real.exp (M*R) := by
        dsimp [D]
        nlinarith [mul_pos hM (Real.exp_pos (M*R)),contourNormalization_nonneg]
  by_cases ha : a=0
  · change a≤_
    rw [ha]
    exact (Real.exp_pos _).le
  have ha0 : 0<a := lt_of_le_of_ne (analyticContourSize_nonneg _ _) (Ne.symm ha)
  have hl := Real.log_le_log (pow_pos ha0 2) hs
  rw [Real.log_pow,Real.log_mul (mul_ne_zero hD0.ne' hM.ne') (Real.exp_ne_zero _),
    Real.log_mul hD0.ne' hM.ne',Real.log_exp] at hl
  change a≤Real.exp ((M*R+Real.log M+Real.log D)/2)
  apply (Real.log_le_iff_le_exp ha0).mp
  norm_num only [Nat.cast_ofNat] at hl
  linarith
end OddZeta.FourValue

import FourValueAnalyticTail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory

theorem centeredDenominator_regular_right (a : ℕ) (z : ℂ) (hz : (a:ℝ)<z.re) :
    (centeredDenominator (K:=ℂ) a).eval z≠0 := by
  intro h
  obtain ⟨j,hj₀,hj₁,hj⟩ := (centeredDenominator_eval_zero_iff a z).mp h
  have hle : (j:ℝ)≤a := by exact_mod_cast hj₁
  have hre : z.re=(j:ℝ) := by rw [hj]; simp
  rw [hre] at hz
  linarith

theorem analyticZetaDenominator_regular_right (n : ℕ) (z : ℂ) (hz : (67*n:ℕ)<z.re) :
    (tupleDenominator (K:=ℂ) (targetEndpointTuple n)).eval z≠0 := by
  simp only [tupleDenominator,eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply centeredDenominator_regular_right
  have hi : (targetEndpointTuple n i:ℝ)≤(67*n:ℕ) := by exact_mod_cast targetEndpointTuple_le_67 n i
  linarith

theorem analyticZetaFunction_continuousOn (n : ℕ) (P : ℂ[X]) :
    ContinuousOn (analyticZetaFunction n P) {z : ℂ | (67*n:ℕ)<z.re} := by
  unfold analyticZetaFunction targetZetaFunction
  exact (Polynomial.continuous _).continuousOn.div (Polynomial.continuous _).continuousOn
    (fun z hz => analyticZetaDenominator_regular_right n z hz)

theorem analyticZetaFunction_partialFractions (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) : ∃ c : ℤ→Fin 10→ℂ,
      ∀ z : ℂ, (100*n:ℕ)<z.re → analyticZetaFunction n P z=partialFractionValue (100*n) c 0 z := by
  obtain ⟨c,hc⟩ := targetZetaTest_partialFractions n (analyticCoordinate P)
    (by simpa [analyticCoordinate_natDegree] using hP)
  refine ⟨c,fun z hz => ?_⟩
  have hreg := analyticZetaDenominator_regular_right n z (by
    have : ((67*n:ℕ):ℝ)≤(100*n:ℕ) := by exact_mod_cast (show 67*n≤100*n by omega)
    linarith)
  have hv := rationalCoefficientAt_regular_zero z (targetZetaNumerator n (analyticCoordinate P))
    (tupleDenominator (targetEndpointTuple n)) hreg
  rw [← targetZetaTest_fraction] at hv
  have hp := rationalCoefficientAt_partialFraction_regular (100*n) 0 _ c hc z
    (partialFraction_support_of_regular _ _ c hc _ _ (targetZetaTest_fraction n _) z hreg)
  exact hv.symm.trans (by simpa using hp)

theorem norm_sub_int_lower (b : ℕ) (z : ℂ) (hz : (b:ℝ)+1/2≤z.re)
    (j : ℤ) (hj : j∈poleWindow b) : 1/2≤‖z-(j:ℂ)‖ := by
  have hj' : j≤(b:ℤ) := (Finset.mem_Icc.mp hj).2
  have hjr : (j:ℝ)≤b := by exact_mod_cast hj'
  have h := Complex.re_le_norm (z-(j:ℂ))
  simp only [Complex.sub_re,Complex.intCast_re] at h
  linarith

def partialFractionBound (b : ℕ) (c : ℤ→Fin 10→ℂ) : ℝ :=
  ∑ j∈poleWindow b,∑ k : Fin 10,‖c j k‖*2^(k.val+1)

theorem partialFractionBound_nonneg (b : ℕ) (c : ℤ→Fin 10→ℂ) :
    0≤partialFractionBound b c := by
  unfold partialFractionBound
  positivity

theorem partialFractionValue_bound (b : ℕ) (c : ℤ→Fin 10→ℂ) (z : ℂ)
    (hz : (b:ℝ)+1/2≤z.re) : ‖partialFractionValue b c 0 z‖≤partialFractionBound b c := by
  unfold partialFractionValue partialFractionBound
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hb := norm_sub_int_lower b z hz j hj
  have hp : 0<‖z-(j:ℂ)‖ := by linarith
  have hi : (‖z-(j:ℂ)‖)⁻¹≤2 := by
    rw [inv_eq_one_div,div_le_iff₀ hp]
    linarith
  simpa [poleTaylorValue,norm_div,norm_pow,← inv_pow] using
    (pow_le_pow_left₀ (by positivity : 0≤(‖z-(j:ℂ)‖)⁻¹) hi (k.val+1))

theorem analyticZetaFunction_halfPlane_bound (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) : ∃ B : ℝ, 0≤B ∧ ∀ z : ℂ,
      ((100*n:ℕ):ℝ)+1/2≤z.re → ‖analyticZetaFunction n P z‖≤B := by
  obtain ⟨c,hc⟩ := analyticZetaFunction_partialFractions n P hP
  refine ⟨partialFractionBound (100*n) c,partialFractionBound_nonneg _ _,fun z hz => ?_⟩
  rw [hc z (by linarith)]
  exact partialFractionValue_bound _ _ z hz

theorem upperContourRay_re (n : ℕ) (t : ℝ) :
    (upperContourRay n t).re=(100*n:ℕ)+1/2+(3/5)*t := by
  simp [upperContourRay,baseContourRay]
  ring

theorem lowerContourRay_re (n : ℕ) (t : ℝ) :
    (lowerContourRay n t).re=(100*n:ℕ)+1/2+(3/5)*t := by
  simp [lowerContourRay]

theorem analyticZetaFunction_ray_bounds (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) : ∃ B : ℝ, 0≤B ∧ ∀ t : ℝ,0≤t →
      ‖analyticZetaFunction n P (upperContourRay n t)‖≤B ∧
      ‖analyticZetaFunction n P (lowerContourRay n t)‖≤B := by
  obtain ⟨B,hB,h⟩ := analyticZetaFunction_halfPlane_bound n P hP
  refine ⟨B,hB,fun t ht => ⟨h _ ?_,h _ ?_⟩⟩
  · rw [upperContourRay_re]; linarith
  · rw [lowerContourRay_re]; linarith
end OddZeta.FourValue

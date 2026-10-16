import FourValueVerticalContourIdentity

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory Filter Set
open scoped Topology

def verticalContourIntegrand (n : ℕ) (P : ℂ[X]) (a : ℕ) (t : ℝ) : ℂ :=
  analyticZetaFunction n P (verticalContourLine a t)*contourKernel (verticalContourLine a t)

theorem verticalContourIntegrand_continuous (n a : ℕ) (P : ℂ[X]) :
    Continuous (verticalContourIntegrand n P a) := by
  apply continuousOn_univ.mp
  exact (analyticContourIntegrand_noninteger_differentiableOn n P).continuousOn.comp
    (by unfold verticalContourLine; fun_prop) (fun t _ => verticalContourLine_integerComplement _ _)

theorem verticalContourIntegrand_integrable (n a : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) (ha : 100*n≤a) : Integrable (verticalContourIntegrand n P a) := by
  obtain ⟨B,hB,h⟩ := analyticZetaFunction_halfPlane_bound n P hP
  obtain ⟨C,hC,hc⟩ := contourKernel_vertical_bound
  apply (integrable_contour_exponential.const_mul (B*C)).mono'
    (verticalContourIntegrand_continuous n a P).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  have hcast : ((100*n:ℕ):ℝ)≤a := by exact_mod_cast ha
  have hr := h (verticalContourLine a t) (by
    simpa [verticalContourLine] using add_le_add_right hcast (1/2))
  unfold verticalContourIntegrand
  rw [norm_mul]
  exact (mul_le_mul hr (hc _ t) (norm_nonneg _) hB).trans_eq (by ring)

def verticalContourIntegral (n : ℕ) (P : ℂ[X]) (a : ℕ) : ℂ :=
  ∫ t : ℝ,verticalContourIntegrand n P a t*Complex.I

theorem verticalContourIntegral_truncation (n a : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) (ha : 100*n≤a) :
    Tendsto (fun T : ℝ => ∫ t in -T..T,verticalContourIntegrand n P a t*Complex.I) atTop
      (𝓝 (verticalContourIntegral n P a)) :=
  intervalIntegral_tendsto_integral ((verticalContourIntegrand_integrable n a P hP ha).mul_const _)
    tendsto_neg_atTop_atBot tendsto_id

theorem horizontalContourIntegral_fixed_closing (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) (a b : ℝ) (ha : ((100*n:ℕ):ℝ)+1/2≤a) (hab : a≤b) :
    Tendsto (fun T : ℝ => ∫ x in a..b,horizontalContourIntegrand n P T x) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => ∫ x in a..b,horizontalContourIntegrand n P (-T) x) atTop (𝓝 0) := by
  obtain ⟨B,hB,h⟩ := horizontalContourIntegral_bound n P hP
  have hexp : Tendsto (fun T : ℝ => Real.exp (-2*Real.pi*T)) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (show 0<2*Real.pi by positivity)) using 1 <;> simp [Function.comp_def,mul_assoc,neg_mul]
  have hlim := (hexp.const_mul B).mul_const (b-a)
  simp only [mul_zero,zero_mul] at hlim
  constructor
  · apply squeeze_zero_norm' (a:=fun T => B*Real.exp (-2*Real.pi*T)*(b-a)) _ hlim
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    simpa [abs_of_nonneg (show 0≤T by linarith)] using h a b T ha hab (by rw [abs_of_nonneg (by linarith)]; exact hT)
  · apply squeeze_zero_norm' (a:=fun T => B*Real.exp (-2*Real.pi*T)*(b-a)) _ hlim
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    simpa [abs_neg,abs_of_nonneg (show 0≤T by linarith)] using h a b (-T) ha hab (by rw [abs_neg,abs_of_nonneg (by linarith)]; exact hT)

theorem verticalContourIntegral_far_tendsto_zero (n : ℕ) (P : ℂ[X]) (hP : P.natDegree≤361*n+3) :
    Tendsto (fun N : ℕ => verticalContourIntegral n P (100*n+N+1)) atTop (𝓝 0) := by
  have h := (closingContourIntegral_tendsto_zero n P hP).mul_const Complex.I
  simpa only [mul_zero,zero_mul,verticalContourIntegral,intervalIntegral.integral_mul_const,
    integral_mul_const,verticalContourIntegrand,closingContourIntegrand] using h
end OddZeta.FourValue

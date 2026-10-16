import FourValueContourRayDeformation

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory Filter Set
open scoped Topology

def initialVerticalIntegrand (n : ℕ) (P : ℂ[X]) (t : ℝ) : ℂ :=
  analyticZetaFunction n P (verticalContourLine (100*n:ℕ) t)*
    contourKernel (verticalContourLine (100*n:ℕ) t)

theorem initialVerticalIntegrand_continuous (n : ℕ) (P : ℂ[X]) :
    Continuous (initialVerticalIntegrand n P) := by
  apply continuousOn_univ.mp
  exact (analyticContourIntegrand_noninteger_differentiableOn n P).continuousOn.comp
    (by unfold verticalContourLine; fun_prop) (fun t _ => verticalContourLine_integerComplement _ _)

theorem initialVerticalIntegrand_integrable (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) : Integrable (initialVerticalIntegrand n P) := by
  obtain ⟨B,hB,h⟩ := analyticZetaFunction_halfPlane_bound n P hP
  obtain ⟨C,hC,hc⟩ := contourKernel_vertical_bound
  apply (integrable_contour_exponential.const_mul (B*C)).mono'
    (initialVerticalIntegrand_continuous n P).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  have hr := h (verticalContourLine (100*n:ℕ) t) (by simp [verticalContourLine])
  unfold initialVerticalIntegrand
  rw [norm_mul]
  exact (mul_le_mul hr (hc _ t) (norm_nonneg _) hB).trans_eq (by ring)

theorem truncatedAnalyticContourIntegral_vertical (n : ℕ) (P : ℂ[X]) (T : ℝ) (hT : 0≤T) :
    truncatedAnalyticContourIntegral n P T=(1/(2*(Real.pi:ℂ)*Complex.I))*
      (-(∫ t in -T..T,initialVerticalIntegrand n P t*Complex.I)+
       (∫ x in (((100*n:ℕ):ℝ)+1/2)..(((100*n:ℕ):ℝ)+1/2+(3/5)*T),horizontalContourIntegrand n P (-T) x)-
       (∫ x in (((100*n:ℕ):ℝ)+1/2)..(((100*n:ℕ):ℝ)+1/2+(3/5)*T),horizontalContourIntegrand n P T x)) := by
  have hl := analyticContour_lower_finite_deformation n P T hT
  have hu := analyticContour_upper_finite_deformation n P T hT
  have hc := (initialVerticalIntegrand_continuous n P).mul_const Complex.I
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ:=volume) (-T) 0) (hc.intervalIntegrable (μ:=volume) 0 T)
  unfold truncatedAnalyticContourIntegral
  rw [hl,hu]
  change _= _
  rw [← hs,intervalIntegral.integral_symm (-T) 0]
  dsimp only [initialVerticalIntegrand]
  ring

theorem analyticContourIntegral_eq_vertical (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) :
    analyticContourIntegral n P= -(1/(2*(Real.pi:ℂ)*Complex.I))*
      (∫ t : ℝ,initialVerticalIntegrand n P t*Complex.I) := by
  have hv := intervalIntegral_tendsto_integral
    ((initialVerticalIntegrand_integrable n P hP).mul_const Complex.I)
    tendsto_neg_atTop_atBot tendsto_id
  have hl := horizontalContourIntegral_lower_linear_closing n P hP
    (((100*n:ℕ):ℝ)+1/2) (3/5) le_rfl (by norm_num)
  have hu := horizontalContourIntegral_linear_closing n P hP
    (((100*n:ℕ):ℝ)+1/2) (3/5) le_rfl (by norm_num)
  have hlim := ((hv.neg.add hl).sub hu).const_mul (1/(2*(Real.pi:ℂ)*Complex.I))
  have he : (fun T : ℝ => (1/(2*(Real.pi:ℂ)*Complex.I))*
      (-(∫ t in -T..T,initialVerticalIntegrand n P t*Complex.I)+
       (∫ x in (((100*n:ℕ):ℝ)+1/2)..(((100*n:ℕ):ℝ)+1/2+(3/5)*T),horizontalContourIntegrand n P (-T) x)-
       (∫ x in (((100*n:ℕ):ℝ)+1/2)..(((100*n:ℕ):ℝ)+1/2+(3/5)*T),horizontalContourIntegrand n P T x)))
      =ᶠ[atTop] truncatedAnalyticContourIntegral n P := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    exact (truncatedAnalyticContourIntegral_vertical n P T hT).symm
  have hf := hlim.congr' he
  have hh := tendsto_nhds_unique (truncatedAnalyticContourIntegral_tendsto n P hP) hf
  simpa only [add_zero,sub_zero,mul_neg,neg_mul] using hh
end OddZeta.FourValue

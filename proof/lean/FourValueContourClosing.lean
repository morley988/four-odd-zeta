import FourValueContourDecay

noncomputable section
namespace OddZeta.FourValue
open Polynomial Filter MeasureTheory Set
open scoped Topology

theorem integrable_contour_exponential : Integrable (fun t : ℝ => Real.exp (-2*Real.pi*|t|)) := by
  have hpos : IntegrableOn (fun t : ℝ => Real.exp (-2*Real.pi*|t|)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (show -2*Real.pi<0 by nlinarith [Real.pi_pos]) 0).congr_fun
    · intro t ht
      dsimp only
      rw [abs_of_pos (show 0<t from ht)]
    · exact measurableSet_Ioi
  have hneg : IntegrableOn (fun t : ℝ => Real.exp (-2*Real.pi*|t|)) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic (show 0<2*Real.pi by positivity) 0).congr_fun
    · intro t ht
      dsimp only
      rw [abs_of_nonpos (show t≤0 from ht)]
      congr 1
      ring
    · exact measurableSet_Iic
  have h := hneg.union hpos
  simpa only [Iic_union_Ioi,integrableOn_univ] using h

def closingContourIntegrand (n : ℕ) (P : ℂ[X]) (N : ℕ) (t : ℝ) : ℂ :=
  analyticZetaFunction n P (verticalContourLine (100*n+N+1:ℕ) t)*
    contourKernel (verticalContourLine (100*n+N+1:ℕ) t)

theorem closingContourIntegrand_continuous (n : ℕ) (P : ℂ[X]) (N : ℕ) :
    Continuous (closingContourIntegrand n P N) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hγ : Continuous (verticalContourLine (100*n+N+1:ℕ)) := by unfold verticalContourLine; fun_prop
  have hr : ((67*n:ℕ):ℝ)<(verticalContourLine (100*n+N+1:ℕ) t).re := by
    simp [verticalContourLine]
    push_cast
    have hn : (0:ℝ)≤n := by positivity
    have hN : (0:ℝ)≤N := by positivity
    linarith
  have hR : ContinuousAt (analyticZetaFunction n P) (verticalContourLine (100*n+N+1:ℕ) t) :=
    (analyticZetaFunction_continuousOn n P).continuousAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hr)
  have hK : ContinuousAt contourKernel (verticalContourLine (100*n+N+1:ℕ) t) :=
    contourKernel_continuousOn.continuousAt
      (Complex.isOpen_compl_range_intCast.mem_nhds (verticalContourLine_integerComplement _ _))
  exact (hR.comp hγ.continuousAt).mul (hK.comp hγ.continuousAt)

theorem closingContourIntegrand_integrable (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) (N : ℕ) : Integrable (closingContourIntegrand n P N) := by
  obtain ⟨B,hB,h⟩ := analyticZetaFunction_vertical_decay n P hP
  apply (integrable_contour_exponential.const_mul (B/((N:ℝ)+1))).mono'
    (closingContourIntegrand_continuous n P N).aestronglyMeasurable
  exact Filter.Eventually.of_forall (h N)

theorem closingContourIntegral_bound (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) : ∃ B : ℝ,0≤B ∧ ∀ N : ℕ,
      ‖∫ t : ℝ,closingContourIntegrand n P N t‖≤B/((N:ℝ)+1) := by
  obtain ⟨B,hB,h⟩ := analyticZetaFunction_vertical_decay n P hP
  let J := ∫ t : ℝ,Real.exp (-2*Real.pi*|t|)
  have hJ : 0≤J := integral_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨B*J,mul_nonneg hB hJ,fun N => ?_⟩
  have hb := norm_integral_le_of_norm_le (integrable_contour_exponential.const_mul (B/((N:ℝ)+1)))
    (Filter.Eventually.of_forall (h N))
  rw [integral_const_mul] at hb
  simpa only [closingContourIntegrand,J,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hb

theorem closingContourIntegral_tendsto_zero (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) :
    Tendsto (fun N : ℕ => ∫ t : ℝ,closingContourIntegrand n P N t) atTop (𝓝 0) := by
  obtain ⟨B,hB,h⟩ := closingContourIntegral_bound n P hP
  apply squeeze_zero_norm h
  have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul B
  simpa only [mul_zero,mul_one_div] using ht
end OddZeta.FourValue

import FourValueContourIntegrand

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory

theorem analyticZetaFunction_kernel_integrable (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) (γ : ℝ→ℂ) (hγ : Continuous γ)
    (hre : ∀ t : ℝ,0<t → ((100*n:ℕ):ℝ)+1/2≤(γ t).re)
    (hreg : ∀ t : ℝ,0<t → γ t∈Complex.integerComplement)
    (C : ℝ) (hC : 0≤C) (hk : ∀ t : ℝ,0<t → ‖contourKernel (γ t)‖≤C*Real.exp (-2*Real.pi*t)) :
    IntegrableOn (fun t : ℝ => analyticZetaFunction n P (γ t)*contourKernel (γ t)) (Set.Ioi 0) := by
  obtain ⟨B,hB,hb⟩ := analyticZetaFunction_halfPlane_bound n P hP
  have hc : ContinuousOn (fun t : ℝ => analyticZetaFunction n P (γ t)*contourKernel (γ t)) (Set.Ioi 0) := by
    apply ContinuousOn.mul
    · apply (analyticZetaFunction_continuousOn n P).comp hγ.continuousOn
      intro t ht
      have h := hre t ht
      have hn : ((67*n:ℕ):ℝ)≤(100*n:ℕ) := by exact_mod_cast (show 67*n≤100*n by omega)
      change ((67*n:ℕ):ℝ)<(γ t).re
      linarith
    · exact contourKernel_continuousOn.comp hγ.continuousOn hreg
  have he := (integrableOn_exp_mul_Ioi (show -2*Real.pi<0 by nlinarith [Real.pi_pos]) 0).const_mul (B*C)
  apply he.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul]
  calc
    _ ≤ B*(C*Real.exp (-2*Real.pi*t)) :=
      mul_le_mul (hb _ (hre t ht)) (hk t ht) (norm_nonneg _) hB
    _ = _ := by ring

theorem upperContourRay_integerComplement (n : ℕ) (t : ℝ) (ht : 0≤t) :
    upperContourRay n t∈Complex.integerComplement := by
  unfold upperContourRay
  exact_mod_cast (Complex.add_intCast_mem_integerComplement (100*n:ℕ)).mpr
    (baseContourRay_integerComplement (3/5) t ht)

theorem lowerContourRay_integerComplement (n : ℕ) (t : ℝ) (ht : 0<t) :
    lowerContourRay n t∈Complex.integerComplement := by
  rintro ⟨k,hk⟩
  have hi := congrArg Complex.im hk
  simp [lowerContourRay] at hi
  linarith

theorem analyticZetaFunction_upperContour_integrable (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) :
    IntegrableOn (fun t : ℝ => analyticZetaFunction n P (upperContourRay n t)*
      contourKernel (upperContourRay n t)) (Set.Ioi 0) := by
  obtain ⟨C,hC,hk⟩ := contourKernel_upperRay_bound
  apply analyticZetaFunction_kernel_integrable n P hP (upperContourRay n)
    (by unfold upperContourRay baseContourRay; fun_prop) _ _ C hC
    (fun t ht => hk n t ht.le)
  · intro t ht
    rw [upperContourRay_re]
    linarith
  · exact fun t ht => upperContourRay_integerComplement n t ht.le

theorem analyticZetaFunction_lowerContour_integrable (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) :
    IntegrableOn (fun t : ℝ => analyticZetaFunction n P (lowerContourRay n t)*
      contourKernel (lowerContourRay n t)) (Set.Ioi 0) := by
  obtain ⟨C,hC,hk⟩ := contourKernel_lowerRay_bound
  apply analyticZetaFunction_kernel_integrable n P hP (lowerContourRay n)
    (by unfold lowerContourRay; fun_prop) _ _ C hC
    (fun t ht => hk n t ht.le)
  · intro t ht
    rw [lowerContourRay_re]
    linarith
  · exact fun t ht => lowerContourRay_integerComplement n t ht

def analyticContourIntegral (n : ℕ) (P : ℂ[X]) : ℂ :=
  (1/(2*(Real.pi:ℂ)*Complex.I))*
    ((∫ t in Set.Ioi (0:ℝ),analyticZetaFunction n P (lowerContourRay n t)*
        contourKernel (lowerContourRay n t)*(3/5-Complex.I))-
     (∫ t in Set.Ioi (0:ℝ),analyticZetaFunction n P (upperContourRay n t)*
        contourKernel (upperContourRay n t)*(3/5+Complex.I)))

/-- Both parameterized, oriented ray integrals are genuine Bochner integrals. -/
theorem analyticContourIntegral_integrable (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) :
    IntegrableOn (fun t : ℝ => analyticZetaFunction n P (lowerContourRay n t)*
        contourKernel (lowerContourRay n t)*(3/5-Complex.I)) (Set.Ioi 0) ∧
    IntegrableOn (fun t : ℝ => analyticZetaFunction n P (upperContourRay n t)*
        contourKernel (upperContourRay n t)*(3/5+Complex.I)) (Set.Ioi 0) :=
  ⟨(analyticZetaFunction_lowerContour_integrable n P hP).mul_const _,
   (analyticZetaFunction_upperContour_integrable n P hP).mul_const _⟩
end OddZeta.FourValue

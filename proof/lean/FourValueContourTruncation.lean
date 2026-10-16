import FourValueContourClosing

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory Filter Set
open scoped Topology

def truncatedAnalyticContourIntegral (n : ℕ) (P : ℂ[X]) (T : ℝ) : ℂ :=
  (1/(2*(Real.pi:ℂ)*Complex.I))*
    ((∫ t in (0:ℝ)..T,analyticZetaFunction n P (lowerContourRay n t)*
        contourKernel (lowerContourRay n t)*(3/5-Complex.I))-
     (∫ t in (0:ℝ)..T,analyticZetaFunction n P (upperContourRay n t)*
        contourKernel (upperContourRay n t)*(3/5+Complex.I)))

theorem truncatedAnalyticContourIntegral_tendsto (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) :
    Tendsto (truncatedAnalyticContourIntegral n P) atTop (𝓝 (analyticContourIntegral n P)) := by
  obtain ⟨hl,hu⟩ := analyticContourIntegral_integrable n P hP
  exact ((intervalIntegral_tendsto_integral_Ioi 0 hl tendsto_id).sub
    (intervalIntegral_tendsto_integral_Ioi 0 hu tendsto_id)).const_mul _

theorem closingContourIntegral_truncation (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) (N : ℕ) :
    Tendsto (fun T : ℝ => ∫ t in -T..T,closingContourIntegrand n P N t) atTop
      (𝓝 (∫ t : ℝ,closingContourIntegrand n P N t)) :=
  intervalIntegral_tendsto_integral (closingContourIntegrand_integrable n P hP N)
    tendsto_neg_atTop_atBot tendsto_id

def contourKernelTailConstant : ℝ :=
  (2*Real.pi)^5/24*fourthPowerMajorant (Real.exp (-2*Real.pi))

theorem contourKernelTailConstant_nonneg : 0≤contourKernelTailConstant := by
  unfold contourKernelTailConstant
  apply mul_nonneg (by positivity)
  exact fourthPowerMajorant_nonneg _ (Real.exp_pos _).le

theorem contourKernel_absolute_im_bound (z : ℂ) (hz : 1≤|z.im|) :
    ‖contourKernel z‖≤contourKernelTailConstant*Real.exp (-2*Real.pi*|z.im|) := by
  by_cases hi : 0≤z.im
  · rw [abs_of_nonneg hi] at hz ⊢
    exact contourKernel_upper_bound z hz
  · have hneg : 1≤(-z).im := by simpa [abs_of_neg (lt_of_not_ge hi)] using hz
    have h := contourKernel_upper_bound (-z) hneg
    simpa [contourKernelTailConstant,contourKernel_neg,abs_of_neg (lt_of_not_ge hi)] using h

def horizontalContourIntegrand (n : ℕ) (P : ℂ[X]) (T x : ℝ) : ℂ :=
  analyticZetaFunction n P ((x:ℂ)+(T:ℂ)*Complex.I)*
    contourKernel ((x:ℂ)+(T:ℂ)*Complex.I)

theorem horizontalContourIntegral_bound (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) : ∃ B : ℝ,0≤B ∧ ∀ a b T : ℝ,
      ((100*n:ℕ):ℝ)+1/2≤a → a≤b → 1≤|T| →
      ‖∫ x in a..b,horizontalContourIntegrand n P T x‖≤B*Real.exp (-2*Real.pi*|T|)*(b-a) := by
  obtain ⟨B,hB,h⟩ := analyticZetaFunction_halfPlane_bound n P hP
  refine ⟨B*contourKernelTailConstant,mul_nonneg hB contourKernelTailConstant_nonneg,fun a b T ha hab hT => ?_⟩
  have hb : ∀ x∈Set.uIoc a b,‖horizontalContourIntegrand n P T x‖≤
      B*contourKernelTailConstant*Real.exp (-2*Real.pi*|T|) := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have hr : ((100*n:ℕ):ℝ)+1/2≤((x:ℂ)+(T:ℂ)*Complex.I).re := by
      simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
        Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
      linarith [hx.1]
    have hk := contourKernel_absolute_im_bound ((x:ℂ)+(T:ℂ)*Complex.I) (by simpa using hT)
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,
      Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at hk
    unfold horizontalContourIntegrand
    rw [norm_mul]
    exact (mul_le_mul (h _ hr) hk (norm_nonneg _) hB).trans_eq (by ring)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using
    intervalIntegral.norm_integral_le_of_norm_le_const hb
theorem contour_linear_exponential_tendsto_zero :
    Tendsto (fun T : ℝ => T*Real.exp (-2*Real.pi*T)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.const_mul_atTop (show 0<2*Real.pi by positivity))
  have hh := h.div_const (2*Real.pi)
  convert hh using 1
  · funext T
    simp only [Function.comp_def,pow_one,id_eq]
    field_simp
  · simp

theorem horizontalContourIntegral_linear_closing (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) (a κ : ℝ)
    (ha : ((100*n:ℕ):ℝ)+1/2≤a) (hκ : 0≤κ) :
    Tendsto (fun T : ℝ => ∫ x in a..(a+κ*T),horizontalContourIntegrand n P T x) atTop (𝓝 0) := by
  obtain ⟨B,hB,h⟩ := horizontalContourIntegral_bound n P hP
  apply squeeze_zero_norm' (a:=fun T : ℝ => (B*κ)*(T*Real.exp (-2*Real.pi*T)))
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    have hb := h a (a+κ*T) T ha (by nlinarith) (by rw [abs_of_nonneg (by linarith)]; exact hT)
    rw [abs_of_nonneg (by linarith)] at hb
    convert hb using 1 <;> ring
  · simpa only [mul_zero] using contour_linear_exponential_tendsto_zero.const_mul (B*κ)

theorem horizontalContourIntegral_lower_linear_closing (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) (a κ : ℝ)
    (ha : ((100*n:ℕ):ℝ)+1/2≤a) (hκ : 0≤κ) :
    Tendsto (fun T : ℝ => ∫ x in a..(a+κ*T),horizontalContourIntegrand n P (-T) x) atTop (𝓝 0) := by
  obtain ⟨B,hB,h⟩ := horizontalContourIntegral_bound n P hP
  apply squeeze_zero_norm' (a:=fun T : ℝ => (B*κ)*(T*Real.exp (-2*Real.pi*T)))
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    have hb := h a (a+κ*T) (-T) ha (by nlinarith) (by rw [abs_neg,abs_of_nonneg (by linarith)]; exact hT)
    rw [abs_neg,abs_of_nonneg (by linarith)] at hb
    convert hb using 1 <;> ring
  · simpa only [mul_zero] using contour_linear_exponential_tendsto_zero.const_mul (B*κ)

end OddZeta.FourValue

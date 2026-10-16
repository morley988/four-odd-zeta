import FourValueWeightEndpointBounds
import FourValueRootIntegralShift

noncomputable section
namespace OddZeta.FourValue

def weightUniformConstant : ℝ := weightEndpointConstant+(5/2)*(Real.log 3+Real.log 2+1)

theorem targetWeightPotential_shift_bound (z : ℂ) (hz : 1≤z.re) (hzi : z.im≠0)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    targetWeightPotential (z+(ε:ℂ))-targetWeightPotential z≤
      5*ε*(Real.log (‖z‖+2)-Real.log ε+1) := by
  have hnum := rootLogIntegral_unit_shift_bound z hz hzi ε hε hε1
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin 15) _ =>
    rootLogIntegral_shift_mono z (targetAlpha i) ε (targetAlpha_bounds i).1
      (by linarith [(targetAlpha_bounds i).2]) hε.le)
  unfold targetWeightPotential
  linarith

theorem normalizedContourPoint_log_growth (y : ℝ) (hy : 0≤y) :
    Real.log (‖normalizedContourPoint y‖+2)≤Real.log 3+Real.log (1+y) := by
  have h := Real.log_le_log (show 0<‖normalizedContourPoint y‖+2 by positivity)
    (show ‖normalizedContourPoint y‖+2≤3*(1+y) by linarith [normalizedContourPoint_norm y hy])
  rwa [Real.log_mul (by norm_num) (by positivity)] at h

theorem analyticWeight_uniform_log_bound (n : ℕ) (hn : 1≤n) (y : ℝ) (hy : 0<y) :
    Real.log ‖analyticZetaFunction n 1 (upperContourRay n (100*(n:ℝ)*y))‖≤
      (100*(n:ℝ))*targetWeightPotential (normalizedContourPoint y)-
      (13/2)*Real.log (100*(n:ℝ))+weightUniformConstant+(17/2)*Real.log (1+y) := by
  let M : ℝ := 100*(n:ℝ)
  have hM : 1≤M := by dsimp [M]; exact_mod_cast (show 1≤100*n by omega)
  have hM0 : 0<M := by linarith
  have he : 0<(1:ℝ)/(2*M) := by positivity
  have he1 : (1:ℝ)/(2*M)≤1 := (div_le_one (by positivity)).mpr (by linarith)
  have hw := analyticWeight_shifted_endpoint_bound n hn y (1/(2*M)) hy.le he he1
  have hp := targetWeightPotential_shift_bound (normalizedContourPoint y)
    (by simp only [normalizedContourPoint,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.one_re,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero]; linarith)
    (by simpa [normalizedContourPoint] using hy.ne') (1/(2*M)) he he1
  have hlog : Real.log ((1:ℝ)/(2*M))= -Real.log 2-Real.log M := by
    rw [Real.log_div (by norm_num) (by positivity),Real.log_one,Real.log_mul (by norm_num) hM0.ne']
    ring
  rw [hlog] at hp
  have hpM := mul_le_mul_of_nonneg_left hp hM0.le
  have heq : M*(5*(1/(2*M)))=5/2 := by field_simp
  have hpM' : M*(targetWeightPotential (normalizedContourPoint y+(1/(2*M):ℝ))-
      targetWeightPotential (normalizedContourPoint y))≤
      (5/2)*(Real.log (‖normalizedContourPoint y‖+2)+Real.log 2+Real.log M+1) := by
    calc
      _ ≤ M*(5*(1/(2*M))*(Real.log (‖normalizedContourPoint y‖+2)-(-Real.log 2-Real.log M)+1)) := hpM
      _ = _ := by rw [← mul_assoc,heq]; ring
  rw [upperContourRay_scaled n hn]
  change Real.log ‖analyticZetaFunction n 1 ((100*(n:ℂ))*(normalizedContourPoint y+(1/(2*M):ℝ)))‖≤_
  unfold weightUniformConstant
  change _≤M*targetWeightPotential (normalizedContourPoint y)-(13/2)*Real.log M+
    (weightEndpointConstant+(5/2)*(Real.log 3+Real.log 2+1))+(17/2)*Real.log (1+y)
  change _≤M*targetWeightPotential (normalizedContourPoint y+(1/(2*M):ℝ))-
    9*Real.log M+weightEndpointConstant+6*Real.log (1+y) at hw
  have hg := normalizedContourPoint_log_growth y hy.le
  nlinarith
end OddZeta.FourValue

import FourValueUniformAsymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

noncomputable section
namespace OddZeta.FourValue
open MeasureTheory Set

def certificateJ (u y : ℝ) : ℝ := (u/2)*Real.log (u^2+y^2)-u+y*Real.arctan (u/y)

def certificateG (y : ℝ) : ℝ := targetNormalizationEntropy+
  5*(certificateJ (1+(3/5)*y+1) y-certificateJ (1+(3/5)*y-1) y)-
  ∑ i : Fin 15,(certificateJ (1+(3/5)*y+targetAlpha i) y-
    certificateJ (1+(3/5)*y-targetAlpha i) y)

theorem certificateJ_hasDerivAt (y u : ℝ) (hy : 0<y) :
    HasDerivAt (fun x => certificateJ x y) ((1/2)*Real.log (u^2+y^2)) u := by
  have hq : u^2+y^2≠0 := ne_of_gt (by nlinarith [sq_nonneg u,sq_pos_of_pos hy])
  have hlog := (((hasDerivAt_id u).pow 2).add_const (y^2)).log hq
  have h := ((((hasDerivAt_id u).div_const 2).mul hlog).sub (hasDerivAt_id u)).add
    (((hasDerivAt_id u).div_const y).arctan.const_mul y)
  convert! h using 1
  dsimp only [id_eq,Pi.pow_apply]
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
  field_simp
  <;> ring

theorem rootLogProfile_log_square (z : ℂ) (t : ℝ) (hz : z.im≠0) :
    rootLogProfile z t=(1/2)*Real.log ((z.re-t)^2+z.im^2) := by
  have he := Complex.sq_norm (z-(t:ℂ))
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at he
  rw [← pow_two,← pow_two] at he
  have h := Real.log_pow ‖z-(t:ℂ)‖ 2
  rw [he] at h
  norm_num only [Nat.cast_ofNat] at h
  unfold rootLogProfile
  linarith

theorem rootLogIntegral_eq_certificateJ (z : ℂ) (a : ℝ) (hz : 0<z.im) :
    rootLogIntegral z a=certificateJ (z.re+a) z.im-certificateJ (z.re-a) z.im := by
  have hc : Continuous (fun u : ℝ => (1/2)*Real.log (u^2+z.im^2)) := by
    apply continuous_const.mul
    apply Continuous.log
    · fun_prop
    · intro u
      nlinarith [sq_nonneg u,sq_pos_of_pos hz]
  unfold rootLogIntegral
  simp_rw [rootLogProfile_log_square z _ hz.ne']
  rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => (1/2)*Real.log (u^2+z.im^2)) z.re]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u (_ : u∈uIcc (z.re-a) (z.re- -a)) => certificateJ_hasDerivAt z.im u hz)
    (hc.intervalIntegrable _ _)
  simpa only [sub_neg_eq_add] using h

theorem targetWeightPotential_eq_certificateG (y : ℝ) (hy : 0<y) :
    targetWeightPotential (normalizedContourPoint y)=certificateG y := by
  have hz : 0<(normalizedContourPoint y).im := by simpa [normalizedContourPoint] using hy
  simp only [targetWeightPotential,rootLogIntegral_eq_certificateJ _ _ hz,certificateG]
  simp [normalizedContourPoint]

theorem contourRate_certificate_expression (s y : ℝ) (hy : 0<y) :
    contourRate s y=certificateG y-2*Real.pi*y+
      s*analyticBasisPotential (concreteBasisWeight s) ((normalizedContourPoint y)^2) := by
  rw [contourRate,targetWeightPotential_eq_certificateG y hy]
end OddZeta.FourValue

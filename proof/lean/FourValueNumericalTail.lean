import FourValueCertificatePotential
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
namespace OddZeta.FourValue.Numerical
open MeasureTheory Set

theorem entropyTerm_lower (x : ℝ) (hx : 0<x) : -1≤entropyTerm x := by
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hx) hx.le
  rw [mul_sub,mul_one,mul_inv_cancel₀ hx.ne'] at h
  unfold entropyTerm
  linarith

theorem entropyTerm_nonpos (x : ℝ) (hx : 0<x) (hx2 : x≤2) : entropyTerm x≤0 := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx) hx.le
  have h2 := mul_nonneg hx.le (sub_nonneg.mpr hx2)
  unfold entropyTerm
  nlinarith

theorem normalization_entropy_le_ten : targetNormalizationEntropy≤10 := by
  have ht (i : Fin 10) : entropyTerm (((2*targetFactorialEndpoints i:ℕ):ℝ)/100)≤0 := by
    apply entropyTerm_nonpos
    · have h := targetFactorialEndpoints_positive i
      positivity
    · fin_cases i <;> norm_num [targetFactorialEndpoints]
  have hsum := Finset.sum_nonpos (s := Finset.univ) (fun (i : Fin 10) _ => ht i)
  have hl := entropyTerm_lower (33/100) (by norm_num)
  unfold targetNormalizationEntropy
  linarith

theorem rootLogIntegral_norm_lower (z : ℂ) (a : ℝ) (ha : 0≤a) (ha1 : a≤1)
    (hr : 1<‖z‖) (hi : z.im≠0) :
    2*a*Real.log (‖z‖-1)≤rootLogIntegral z a := by
  have h := intervalIntegral.integral_mono_on (show -a≤a by linarith)
    (intervalIntegrable_const (c:=Real.log (‖z‖-1)))
    ((rootLogProfile_continuous z hi).intervalIntegrable (μ:=volume) _ _)
    (fun t ht => show Real.log (‖z‖-1)≤rootLogProfile z t from by
      apply Real.log_le_log (by linarith)
      have hn := norm_sub_norm_le z (t:ℂ)
      rw [Complex.norm_real,Real.norm_eq_abs] at hn
      have ht' : |t|≤a := abs_le.mpr ht
      linarith)
  rw [intervalIntegral.integral_const] at h
  change (a- -a)*Real.log (‖z‖-1)≤_ at h
  unfold rootLogIntegral
  convert h using 1 <;> ring

theorem weight_norm_bound (z : ℂ) (hr : 1<‖z‖) (hi : z.im≠0) :
    targetWeightPotential z≤10+10*Real.log (‖z‖+1)-(861/50)*Real.log (‖z‖-1) := by
  have hu := rootLogIntegral_const_upper z 1 (‖z‖+1) (by norm_num) hi le_rfl
  have hl (i : Fin 15) := rootLogIntegral_norm_lower z (targetAlpha i)
    (targetAlpha_bounds i).1 (by linarith [(targetAlpha_bounds i).2]) hr hi
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin 15) _ => hl i)
  have ha : ∑ i : Fin 15,targetAlpha i=861/100 := by
    unfold targetAlpha
    rw [← Finset.sum_div,targetEndpointTuple_sum]
    norm_num
  rw [← Finset.sum_mul,← Finset.mul_sum,ha] at hsum
  unfold targetWeightPotential
  linarith [normalization_entropy_le_ten]

theorem log_add_error (r a : ℝ) (hr : 0<r) (ha : 0≤a) :
    Real.log (r+a)≤Real.log r+a/r := by
  have h := Real.log_le_sub_one_of_pos (show 0<(r+a)/r by positivity)
  rw [Real.log_div (by positivity) hr.ne'] at h
  have he : (r+a)/r-1=a/r := by field_simp; ring
  rw [he] at h
  linarith

theorem log_sub_error (r : ℝ) (hr : 1<r) :
    Real.log r-1/(r-1)≤Real.log (r-1) := by
  have h := log_add_error (r-1) 1 (by linarith) (by norm_num)
  have he : r-1+1=r := by ring
  rw [he] at h
  linarith

/-- A deliberately coarse tail bound suffices: every knot height is at least -9.
This avoids relying on the more precise external Arb tail constant. -/
theorem certificate_tail (s y : ℝ) (w : Fin 45→ℝ)
    (hs : 0≤s) (hs1 : s≤basisLimit) (hy : 5≤y)
    (hw : ∀ l,0≤w l) (hw1 : ∑ l,w l=1) :
    certificateG y-2*Real.pi*y+
      s*analyticBasisPotential w ((normalizedContourPoint y)^2)≤-9 := by
  let z := normalizedContourPoint y
  let r := ‖z‖
  have him : z.im=y := by simp [z,normalizedContourPoint]
  have hry : y≤r := by
    have h := Complex.im_le_norm z
    simpa [him,r] using h
  have hr : 5≤r := hy.trans hry
  have hr0 : 0<r := by linarith
  have hz : z.im≠0 := by rw [him]; linarith
  have hg := weight_norm_bound z (by change 1<r; linarith) hz
  have hp := analyticBasisPotential_coarse_bound w hw hw1 (z^2)
  rw [norm_pow] at hp
  change analyticBasisPotential w (z^2)≤2*Real.log (r^2+3) at hp
  have hlog := Real.log_nonneg (show 1≤r by linarith)
  have hlog2 := Real.log_nonneg (show 1≤r^2+3 by nlinarith)
  have hb := mul_le_mul_of_nonneg_left hp hs
  have hs' : s≤361/200 := hs1
  have hb' := mul_le_mul_of_nonneg_right hs' (show 0≤2*Real.log (r^2+3) by linarith)
  have hlplus := log_add_error r 1 hr0 (by norm_num)
  have hlminus := log_sub_error r (by linarith)
  have hlsq := log_add_error (r^2) 3 (by positivity) (by norm_num)
  rw [Real.log_pow] at hlsq
  norm_num only [Nat.cast_ofNat] at hlsq
  have hdiv1 : 1/r≤1/5 := by apply one_div_le_one_div_of_le (by norm_num) hr
  have hdiv2 : 1/(r-1)≤1/4 := by apply one_div_le_one_div_of_le (by norm_num); linarith
  have hdiv3 : 3/r^2≤3/25 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hpi : 3<Real.pi := Real.pi_gt_three
  have hpiy : 30≤2*Real.pi*y := by
    have h := mul_le_mul hpi.le hy (by norm_num : (0:ℝ)≤5) (by linarith : 0≤Real.pi)
    nlinarith
  rw [← targetWeightPotential_eq_certificateG y (by linarith)]
  change targetWeightPotential z-2*Real.pi*y+s*analyticBasisPotential w (z^2)≤-9
  change targetWeightPotential z≤10+10*Real.log (r+1)-(861/50)*Real.log (r-1) at hg
  nlinarith

end OddZeta.FourValue.Numerical

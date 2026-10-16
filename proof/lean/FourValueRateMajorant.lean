import FourValueUniformDensity

noncomputable section
namespace OddZeta.FourValue
open MeasureTheory Set

def contourRateMajorantConstant : ℝ := targetNormalizationEntropy+10*Real.log 2-
  (861/50)*Real.log (33/100)+4*Real.log 4

theorem rootLogIntegral_const_upper (z : ℂ) (a B : ℝ) (ha : 0≤a) (hzi : z.im≠0)
    (hB : ‖z‖+a≤B) : rootLogIntegral z a≤2*a*Real.log B := by
  have hc := rootLogProfile_continuous z hzi
  have h := intervalIntegral.integral_mono_on (show -a≤a by linarith)
    (hc.intervalIntegrable (μ:=volume) _ _) (intervalIntegrable_const (c:=Real.log B))
    (fun t ht => show rootLogProfile z t≤Real.log B from by
      apply Real.log_le_log
      · apply norm_pos_iff.mpr
        intro he
        have hi := congrArg Complex.im (sub_eq_zero.mp he)
        exact hzi (by simpa using hi)
      · have h := norm_sub_le z (t:ℂ)
        rw [Complex.norm_real,Real.norm_eq_abs] at h
        have ht' : |t|≤a := abs_le.mpr ht
        linarith)
  rw [intervalIntegral.integral_const] at h
  change _≤(a- -a)*Real.log B at h
  unfold rootLogIntegral
  convert h using 1 <;> ring

theorem rootLogIntegral_const_lower (z : ℂ) (a d : ℝ) (ha : 0≤a) (hd : 0<d)
    (hz : a+d≤z.re) : 2*a*Real.log d≤rootLogIntegral z a := by
  have hi := rootLogProfile_intervalIntegrable z a ha (by linarith)
  have h := intervalIntegral.integral_mono_on (show -a≤a by linarith)
    (intervalIntegrable_const (c:=Real.log d)) hi
    (fun t ht => show Real.log d≤rootLogProfile z t from by
      apply Real.log_le_log hd
      have h := Complex.re_le_norm (z-(t:ℂ))
      simp only [Complex.sub_re,Complex.ofReal_re] at h
      linarith [ht.2])
  rw [intervalIntegral.integral_const] at h
  change (a- -a)*Real.log d≤_ at h
  unfold rootLogIntegral
  convert h using 1 <;> ring

theorem targetWeightPotential_coarse_bound (y : ℝ) (hy : 0<y) :
    targetWeightPotential (normalizedContourPoint y)≤
      targetNormalizationEntropy+10*Real.log 2-(861/50)*Real.log (33/100)+10*Real.log (1+y) := by
  have hz : (normalizedContourPoint y).im≠0 := by simpa [normalizedContourPoint] using hy.ne'
  have hnum := rootLogIntegral_const_upper (normalizedContourPoint y) 1 (2*(1+y)) (by norm_num) hz
    (by linarith [normalizedContourPoint_norm y hy.le])
  have hden (i : Fin 15) := rootLogIntegral_const_lower (normalizedContourPoint y)
    (targetAlpha i) (33/100) (targetAlpha_bounds i).1 (by norm_num)
    (by simp only [normalizedContourPoint,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.one_re,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero]; linarith [(targetAlpha_bounds i).2])
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin 15) _ => hden i)
  have ha : ∑ i : Fin 15,targetAlpha i=861/100 := by
    unfold targetAlpha
    rw [← Finset.sum_div,targetEndpointTuple_sum]
    norm_num
  rw [← Finset.sum_mul,← Finset.mul_sum,ha] at hsum
  rw [Real.log_mul (by norm_num) (by positivity)] at hnum
  unfold targetWeightPotential
  linarith

theorem analyticBasisPotential_coarse_bound (w : Fin 45→ℝ) (hw : ∀ l,0≤w l)
    (hs : ∑ l,w l=1) (Z : ℂ) :
    analyticBasisPotential w Z≤2*Real.log (‖Z‖+3) := by
  have hc (l : Fin 45) : ‖analyticCenter l‖≤3 := by
    have h := analyticCenter_bound l
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have hd (l : Fin 45) : analyticDistance Z l≤(‖Z‖+3)^2 := by
    unfold analyticDistance
    rw [pow_two]
    apply mul_le_mul
    · apply max_le
      · exact (norm_sub_le _ _).trans (add_le_add (le_refl ‖Z‖) (hc l))
      · change (1/50:ℝ)≤‖Z‖+3
        linarith [norm_nonneg Z]
    · apply max_le
      · have h := norm_sub_le Z (star (analyticCenter l))
        simp only [norm_star] at h
        linarith [hc l]
      · change (1/50:ℝ)≤‖Z‖+3
        linarith [norm_nonneg Z]
    · exact le_trans (norm_nonneg _) (le_max_left _ _)
    · positivity
  have hl (l : Fin 45) : Real.log (analyticDistance Z l)≤2*Real.log (‖Z‖+3) := by
    have h := Real.log_le_log (by have := analyticDistance_lower Z l; linarith) (hd l)
    rwa [Real.log_pow] at h
  unfold analyticBasisPotential
  calc
    _ ≤ ∑ l,w l*(2*Real.log (‖Z‖+3)) := Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (hl l) (hw l))
    _ = _ := by rw [← Finset.sum_mul,hs,one_mul]

theorem contourRate_coarse_bound (s y : ℝ) (hs : 0≤s) (hs1 : s≤basisLimit) (hy : 0<y) :
    contourRate s y≤contourRateMajorantConstant+18*Real.log (1+y)-2*Real.pi*y := by
  have hp := analyticBasisPotential_coarse_bound (concreteBasisWeight s)
    (concreteBasisWeight_nonneg s hs hs1) (concreteBasisWeight_sum s hs hs1)
    ((normalizedContourPoint y)^2)
  have hnorm : ‖(normalizedContourPoint y)^2‖+3≤4*(1+y)^2 := by
    rw [norm_pow]
    have h := normalizedContourPoint_norm y hy.le
    nlinarith [norm_nonneg (normalizedContourPoint y)]
  have hl := Real.log_le_log (show 0<‖(normalizedContourPoint y)^2‖+3 by positivity) hnorm
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hlog4 := Real.log_nonneg (show (1:ℝ)≤4 by norm_num)
  have hlogy := Real.log_nonneg (show (1:ℝ)≤1+y by linarith)
  have hmul := mul_le_mul_of_nonneg_left hp hs
  have hs2 : s≤2 := by unfold basisLimit at hs1; linarith
  have hb : s*(2*Real.log 4+4*Real.log (1+y))≤4*Real.log 4+8*Real.log (1+y) := by
    have h := mul_le_mul_of_nonneg_right hs2
      (show 0≤2*Real.log 4+4*Real.log (1+y) by linarith)
    linarith
  have hmul' := mul_le_mul_of_nonneg_left hl hs
  have hw := targetWeightPotential_coarse_bound y hy
  unfold contourRate contourRateMajorantConstant
  nlinarith
end OddZeta.FourValue

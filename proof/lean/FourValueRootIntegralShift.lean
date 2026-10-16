import FourValueScaledRootIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
namespace OddZeta.FourValue
open MeasureTheory Set

theorem rootLogProfile_continuous (z : ℂ) (hz : z.im≠0) : Continuous (rootLogProfile z) := by
  apply Continuous.log
  · fun_prop
  · intro t
    apply norm_ne_zero_iff.mpr
    intro he
    have h := congrArg Complex.im (sub_eq_zero.mp he)
    simp only [Complex.ofReal_im] at h
    exact hz h

theorem rootLogIntegral_shift_translation (z : ℂ) (ε a : ℝ) :
    rootLogIntegral (z+(ε:ℂ)) a=∫ t in -a-ε..a-ε,rootLogProfile z t := by
  unfold rootLogIntegral
  rw [← intervalIntegral.integral_comp_sub_right (rootLogProfile z) ε]
  apply intervalIntegral.integral_congr
  intro t ht
  unfold rootLogProfile
  congr 2
  push_cast
  ring

theorem rootLogIntegral_unit_shift_bound (z : ℂ) (hz : 1≤z.re) (hzi : z.im≠0)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    rootLogIntegral (z+(ε:ℂ)) 1-rootLogIntegral z 1≤
      ε*(Real.log (‖z‖+2)-Real.log ε+1) := by
  have hc := rootLogProfile_continuous z hzi
  have hsplit := intervalIntegral.integral_interval_sub_interval_comm
    (hc.intervalIntegrable (μ:=volume) (-1-ε) (1-ε)) (hc.intervalIntegrable (μ:=volume) (-1) 1)
    (hc.intervalIntegrable (μ:=volume) (-1-ε) (-1))
  have hupper : (∫ t in -1-ε..-1,rootLogProfile z t)≤ε*Real.log (‖z‖+2) := by
    have h := intervalIntegral.integral_mono_on (show -1-ε≤(-1:ℝ) by linarith)
      (hc.intervalIntegrable (μ:=volume) _ _) (intervalIntegrable_const (c:=Real.log (‖z‖+2)))
      (fun t ht => show rootLogProfile z t≤Real.log (‖z‖+2) from by
        apply Real.log_le_log
        · exact rootLogProfile_norm_pos z t (by linarith [ht.2])
        · have h := norm_sub_le z (t:ℂ)
          rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith [ht.2])] at h
          linarith [ht.1])
    rw [intervalIntegral.integral_const] at h
    simp only [smul_eq_mul] at h
    convert h using 1 <;> ring
  have hlog : IntervalIntegrable (fun t : ℝ => Real.log (1-t)) volume (1-ε) 1 := by
    convert (intervalIntegral.intervalIntegrable_log' (a:=ε) (b:=0)).comp_sub_left 1 using 1 <;> ring
  have hlower : ε*Real.log ε-ε≤∫ t in 1-ε..1,rootLogProfile z t := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo (show 1-ε≤(1:ℝ) by linarith)
      hlog (hc.intervalIntegrable (μ:=volume) _ _) (fun t ht => show Real.log (1-t)≤rootLogProfile z t from by
        apply Real.log_le_log (by linarith [ht.2])
        have h := Complex.re_le_norm (z-(t:ℂ))
        simp only [Complex.sub_re,Complex.ofReal_re] at h
        linarith)
    rw [intervalIntegral.integral_comp_sub_left,integral_log] at h
    norm_num at h
    simpa using h
  rw [rootLogIntegral_shift_translation]
  change (∫ t in -1-ε..1-ε,rootLogProfile z t)-(∫ t in -1..1,rootLogProfile z t)≤_
  rw [hsplit]
  nlinarith
theorem rootLogProfile_shift_mono (z : ℂ) (t ε : ℝ) (ht : t<z.re) (hε : 0≤ε) :
    rootLogProfile z t≤rootLogProfile (z+(ε:ℂ)) t := by
  apply Real.log_le_log (rootLogProfile_norm_pos z t ht)
  have h1 := Complex.sq_norm (z-(t:ℂ))
  have h2 := Complex.sq_norm (z+(ε:ℂ)-(t:ℂ))
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.add_re,
    Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero,add_zero] at h1 h2
  nlinarith [norm_nonneg (z-(t:ℂ)),norm_nonneg (z+(ε:ℂ)-(t:ℂ)),mul_nonneg hε (show 0≤z.re-t by linarith)]

theorem rootLogIntegral_shift_mono (z : ℂ) (a ε : ℝ) (ha : 0≤a) (hz : a<z.re) (hε : 0≤ε) :
    rootLogIntegral z a≤rootLogIntegral (z+(ε:ℂ)) a := by
  apply intervalIntegral.integral_mono_on (show -a≤a by linarith)
    (rootLogProfile_intervalIntegrable z a ha hz)
    (rootLogProfile_intervalIntegrable (z+(ε:ℂ)) a ha (by simp only [Complex.add_re,Complex.ofReal_re]; linarith))
  intro t ht
  exact rootLogProfile_shift_mono z t ε (lt_of_le_of_lt ht.2 hz) hε
end OddZeta.FourValue

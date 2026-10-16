import FourValueRootLogProfile

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory Set

def rootLogIntegral (z : ℂ) (a : ℝ) : ℝ := ∫ t in -a..a,rootLogProfile z t

theorem rootLogProfile_continuousOn (z : ℂ) (a b : ℝ) (hb : b<z.re) :
    ContinuousOn (rootLogProfile z) (Icc a b) := by
  apply ContinuousOn.log
  · fun_prop
  · intro t ht
    exact (rootLogProfile_norm_pos z t (lt_of_le_of_lt ht.2 hb)).ne'

theorem rootLogProfile_intervalIntegrable (z : ℂ) (a : ℝ) (ha : 0≤a) (hz : a<z.re) :
    IntervalIntegrable (rootLogProfile z) volume (-a) a := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith)]
  exact rootLogProfile_continuousOn z (-a) a hz

theorem rootLogProfile_scale (M : ℝ) (hM : 0<M) (z : ℂ) (t : ℝ) (ht : t/M<z.re) :
    rootLogProfile ((M:ℂ)*z) t=Real.log M+rootLogProfile z (t/M) := by
  unfold rootLogProfile
  have he : (M:ℂ)*z-(t:ℂ)=(M:ℂ)*(z-((t/M:ℝ):ℂ)) := by
    push_cast
    field_simp [show (M:ℂ)≠0 by exact_mod_cast hM.ne']
    <;> ring
  rw [he,norm_mul,Real.log_mul (by simpa using hM.ne') (rootLogProfile_norm_pos z (t/M) ht).ne']
  simp [abs_of_pos hM]

theorem rootLogIntegral_scale (M : ℝ) (hM : 0<M) (z : ℂ) (a : ℝ)
    (ha : 0≤a) (hz : a/M<z.re) :
    rootLogIntegral ((M:ℂ)*z) a=2*a*Real.log M+M*rootLogIntegral z (a/M) := by
  have hcont : ContinuousOn (fun t : ℝ => rootLogProfile z (t/M)) (Icc (-a) a) := by
    apply ContinuousOn.log
    · fun_prop
    · intro t ht
      exact (rootLogProfile_norm_pos z (t/M) (lt_of_le_of_lt ((div_le_div_iff_of_pos_right hM).mpr ht.2) hz)).ne'
  have hi : IntervalIntegrable (fun t : ℝ => rootLogProfile z (t/M)) volume (-a) a := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (show -a≤a by linarith)] using hcont
  unfold rootLogIntegral
  rw [intervalIntegral.integral_congr (g:=fun t => Real.log M+rootLogProfile z (t/M))]
  · rw [intervalIntegral.integral_add intervalIntegrable_const hi,intervalIntegral.integral_const,
      intervalIntegral.integral_comp_div _ hM.ne']
    simp only [smul_eq_mul,neg_div]
    ring
  · intro t ht
    rw [uIcc_of_le (show -a≤a by linarith)] at ht
    exact rootLogProfile_scale M hM z t
      (lt_of_le_of_lt ((div_le_div_iff_of_pos_right hM).mpr ht.2) hz)

theorem centeredRoot_scaled_log_error (a : ℕ) (M : ℝ) (hM : 0<M) (z : ℂ) (hz : (a:ℝ)/M<z.re) :
    rootLogProfile z ((a:ℝ)/M)≤
      Real.log ‖(centeredDenominator (K:=ℂ) a).eval ((M:ℂ)*z)‖-
        ((2*(a:ℝ)+1)*Real.log M+M*rootLogIntegral z ((a:ℝ)/M)) ∧
    Real.log ‖(centeredDenominator (K:=ℂ) a).eval ((M:ℂ)*z)‖-
        ((2*(a:ℝ)+1)*Real.log M+M*rootLogIntegral z ((a:ℝ)/M))≤rootLogProfile z (-(a:ℝ)/M) := by
  have hz' : (a:ℝ)<((M:ℂ)*z).re := by
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact (div_lt_iff₀ hM).mp hz |>.trans_eq (mul_comm _ _)
  have h := centeredRoot_log_integral_error a ((M:ℂ)*z) hz'
  change rootLogProfile ((M:ℂ)*z) a≤_ - rootLogIntegral ((M:ℂ)*z) a ∧
    _-rootLogIntegral ((M:ℂ)*z) a≤rootLogProfile ((M:ℂ)*z) (-(a:ℝ)) at h
  rw [rootLogIntegral_scale M hM z a (Nat.cast_nonneg a) hz,
    rootLogProfile_scale M hM z a hz,
    rootLogProfile_scale M hM z (-(a:ℝ)) (by have := div_nonneg (Nat.cast_nonneg a) hM.le; rw [neg_div]; linarith)] at h
  constructor <;> linarith [h.1,h.2]
end OddZeta.FourValue

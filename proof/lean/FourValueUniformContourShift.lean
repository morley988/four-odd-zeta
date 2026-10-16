import FourValueConcreteContourComplete

noncomputable section
namespace OddZeta.FourValue

def cutoffDistance (z c : ℂ) : ℝ := max ‖z-c‖ (1/50)

theorem cutoffDistance_pos (z c : ℂ) : 0<cutoffDistance z c :=
  lt_of_lt_of_le (by norm_num : (0:ℝ)<1/50) (le_max_right _ _)

theorem cutoffDistance_shift (z w c : ℂ) : cutoffDistance z c≤cutoffDistance w c+‖z-w‖ := by
  unfold cutoffDistance
  apply max_le
  · have h : ‖z-c‖≤‖z-w‖+‖w-c‖ := by
      convert norm_add_le (z-w) (w-c) using 1
      congr 1
      ring
    have hm := le_max_left ‖w-c‖ (1/50:ℝ)
    linarith
  · have hm := le_max_right ‖w-c‖ (1/50:ℝ)
    linarith [norm_nonneg (z-w)]

theorem squared_shift_norm_bound (z : ℂ) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) :
    ‖(z+(ε:ℂ))^2-z^2‖≤ε*(2*‖z‖+1) := by
  have he : (z+(ε:ℂ))^2-z^2=2*(ε:ℂ)*z+(ε:ℂ)^2 := by ring
  rw [he]
  have h := norm_add_le (2*(ε:ℂ)*z) ((ε:ℂ)^2)
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hε] at h
  nlinarith

theorem squared_shift_cutoff_bound (z c : ℂ) (hc : ‖c‖≤3) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) :
    cutoffDistance ((z+(ε:ℂ))^2) c≤(1+250*ε)*cutoffDistance (z^2) c := by
  have hd := (cutoffDistance_shift ((z+(ε:ℂ))^2) (z^2) c).trans
    (add_le_add le_rfl (squared_shift_norm_bound z ε hε hε1))
  have hv : (1/50:ℝ)≤cutoffDistance (z^2) c := le_max_right _ _
  by_cases hz : ‖z‖≤2
  · nlinarith [mul_nonneg hε (sub_nonneg.mpr hv)]
  · have hn := norm_sub_norm_le (z^2) c
    rw [norm_pow] at hn
    have hm : ‖z^2-c‖≤cutoffDistance (z^2) c := le_max_left _ _
    have hq : 2*‖z‖+1≤250*cutoffDistance (z^2) c := by
      nlinarith [sq_nonneg (‖z‖-2)]
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hq)]

theorem squared_shift_cutoff_log_bound (z c : ℂ) (hc : ‖c‖≤3) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) :
    Real.log (cutoffDistance ((z+(ε:ℂ))^2) c)≤Real.log (cutoffDistance (z^2) c)+250*ε := by
  have h := Real.log_le_log (cutoffDistance_pos _ _) (squared_shift_cutoff_bound z c hc ε hε hε1)
  have he : 0<1+250*ε := by linarith
  rw [Real.log_mul he.ne' (cutoffDistance_pos _ _).ne'] at h
  have hb := Real.log_le_sub_one_of_pos he
  linarith

theorem analyticBasisPotential_squared_shift (w : Fin 45→ℝ) (hw : ∀ l,0≤w l)
    (hs : ∑ l,w l=1) (z : ℂ) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) :
    analyticBasisPotential w ((z+(ε:ℂ))^2)≤analyticBasisPotential w (z^2)+500*ε := by
  have hc (l : Fin 45) : ‖analyticCenter l‖≤3 := by
    have h := analyticCenter_bound l
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have hp (l : Fin 45) : Real.log (analyticDistance ((z+(ε:ℂ))^2) l)≤
      Real.log (analyticDistance (z^2) l)+500*ε := by
    have h1 := squared_shift_cutoff_log_bound z (analyticCenter l) (hc l) ε hε hε1
    have h2 := squared_shift_cutoff_log_bound z (star (analyticCenter l)) (by simpa using hc l) ε hε hε1
    change Real.log (cutoffDistance ((z+(ε:ℂ))^2) (analyticCenter l)*cutoffDistance ((z+(ε:ℂ))^2) (star (analyticCenter l)))≤
      Real.log (cutoffDistance (z^2) (analyticCenter l)*cutoffDistance (z^2) (star (analyticCenter l)))+500*ε
    rw [Real.log_mul (cutoffDistance_pos _ _).ne' (cutoffDistance_pos _ _).ne',
      Real.log_mul (cutoffDistance_pos _ _).ne' (cutoffDistance_pos _ _).ne']
    linarith
  unfold analyticBasisPotential
  calc
    _ ≤ ∑ l,w l*(Real.log (analyticDistance (z^2) l)+500*ε) :=
      Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (hp l) (hw l))
    _ = _ := by simp_rw [mul_add]; rw [Finset.sum_add_distrib,← Finset.sum_mul,hs]; ring
end OddZeta.FourValue

import FourValueContourRays

noncomputable section
namespace OddZeta.FourValue
open Filter Set
open scoped Topology

def regularKernelTerm (n : ℤ) (z : ℂ) : ℂ := if n=0 then 0 else 1/(z+n)^5

def regularKernelPart (z : ℂ) : ℂ := ∑' n : ℤ,regularKernelTerm n z

theorem integer_fifthPower_summable (z : ℂ) : Summable (fun n : ℤ => 1/(z+n)^5) := by
  simpa using EisensteinSeries.linear_right_summable z 1 (k:=5) (by norm_num)

theorem regularKernelTerm_denom_bound (n : ℤ) (hn : n≠0) (z : ℂ) (hz : ‖z‖≤1/2) :
    ‖(n:ℂ)‖/2≤‖z+n‖ := by
  have hn1 : (1:ℝ)≤‖(n:ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast (show (1:ℤ)≤|n| from Int.one_le_abs hn)
  have ht := norm_sub_le (z+(n:ℂ)) z
  simp only [add_sub_cancel_left] at ht
  linarith

theorem regularKernelTerm_bound (n : ℤ) (z : ℂ) (hz : ‖z‖≤1/2) :
    ‖regularKernelTerm n z‖≤32*‖1/(n:ℂ)^5‖ := by
  by_cases hn : n=0
  · simp [regularKernelTerm,hn]
  · have hnC : (n:ℂ)≠0 := by exact_mod_cast hn
    have hp := norm_pos_iff.mpr hnC
    have hb := regularKernelTerm_denom_bound n hn z hz
    have ht : 0<‖z+(n:ℂ)‖ := lt_of_lt_of_le (by positivity) hb
    simp only [regularKernelTerm,if_neg hn,norm_div,norm_one,norm_pow]
    calc
      _ ≤ 1/(‖(n:ℂ)‖/2)^5 := one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hb 5)
      _ = _ := by field_simp; ring

theorem regularKernelTerm_summable_bound : Summable (fun n : ℤ => 32*‖1/(n:ℂ)^5‖) := by
  have h : Summable (fun n : ℤ => ‖1/(n:ℂ)^5‖) := by
    apply (summable_norm_iff).mpr
    simpa using integer_fifthPower_summable 0
  exact h.mul_left 32

theorem regularKernelPart_summableLocallyUniformlyOn :
    SummableLocallyUniformlyOn regularKernelTerm (Metric.ball (0:ℂ) (1/2)) := by
  apply SummableLocallyUniformlyOn_of_locally_bounded Metric.isOpen_ball
  intro K hK hKc
  refine ⟨fun n : ℤ => 32*‖1/(n:ℂ)^5‖,regularKernelTerm_summable_bound,fun n z hz => ?_⟩
  apply regularKernelTerm_bound
  have h := hK hz
  exact (by simpa [Metric.mem_ball,dist_zero_right] using h : ‖z‖<1/2).le

theorem regularKernelPart_differentiableOn :
    DifferentiableOn ℂ regularKernelPart (Metric.ball (0:ℂ) (1/2)) := by
  apply regularKernelPart_summableLocallyUniformlyOn.differentiableOn Metric.isOpen_ball
  intro n z hz
  by_cases hn : n=0
  · change DifferentiableAt ℂ (fun w : ℂ => if n=0 then 0 else 1/(w+n)^5) z
    simp only [regularKernelTerm,if_pos hn]
    fun_prop
  · have hnC : (n:ℂ)≠0 := by exact_mod_cast hn
    have hnorm : 0<‖z+n‖ := lt_of_lt_of_le (by positivity : 0<‖(n:ℂ)‖/2)
      (regularKernelTerm_denom_bound n hn z (by exact (by simpa [Metric.mem_ball,dist_zero_right] using hz : ‖z‖<1/2).le))
    have hne : z+(n:ℂ)≠0 := norm_pos_iff.mp hnorm
    change DifferentiableAt ℂ (fun w : ℂ => if n=0 then 0 else 1/(w+n)^5) z
    simp only [regularKernelTerm,if_neg hn]
    apply DifferentiableAt.div (by fun_prop) (by fun_prop)
    exact pow_ne_zero _ hne
end OddZeta.FourValue

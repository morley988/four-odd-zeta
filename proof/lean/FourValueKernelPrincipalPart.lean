import FourValueKernelRegularPart

noncomputable section
namespace OddZeta.FourValue
open Filter Set
open scoped Topology

theorem integer_fifthPower_series_neg (z : ℂ) :
    (∑' n : ℤ,1/(-z+n)^5)= -(∑' n : ℤ,1/(z+n)^5) := by
  calc
    _ = ∑' n : ℤ,1/(-z+(-n:ℤ))^5 := ((Equiv.neg ℤ).tsum_eq _).symm
    _ = ∑' n : ℤ,-(1/(z+n)^5) := by
      apply tsum_congr
      intro n
      have he : -z+((-n:ℤ):ℂ)= -(z+(n:ℂ)) := by push_cast; ring
      rw [he,show (-(z+(n:ℂ)))^5= -(z+(n:ℂ))^5 by ring,div_neg]
    _ = _ := tsum_neg

theorem contourKernel_integer_series_lower (z : ℂ) (hz : z.im<0) :
    contourKernel z=∑' n : ℤ,1/(z+n)^5 := by
  have h := contourKernel_integer_series (-z) (by simpa using neg_pos.mpr hz)
  rw [contourKernel_neg,integer_fifthPower_series_neg] at h
  exact neg_injective h

theorem contourKernel_principalPart_nonreal (z : ℂ) (hz : z.im≠0) :
    contourKernel z=1/z^5+regularKernelPart z := by
  have hk : contourKernel z=∑' n : ℤ,1/(z+n)^5 := by
    rcases lt_or_gt_of_ne hz with h|h
    · exact contourKernel_integer_series_lower z h
    · exact contourKernel_integer_series z h
  rw [hk,(integer_fifthPower_summable z).tsum_eq_add_tsum_ite 0]
  simp [regularKernelPart,regularKernelTerm]

theorem small_nonzero_integerComplement (z : ℂ) (hz : ‖z‖<1/2) (hz0 : z≠0) :
    z∈Complex.integerComplement := by
  rintro ⟨n,rfl⟩
  have hn : n≠0 := by exact_mod_cast hz0
  have h1 : (1:ℝ)≤‖(n:ℂ)‖ := by rw [Complex.norm_intCast]; exact_mod_cast Int.one_le_abs hn
  linarith

theorem contourKernel_principalPart (z : ℂ) (hz : ‖z‖<1/2) (hz0 : z≠0) :
    contourKernel z=1/z^5+regularKernelPart z := by
  by_cases hi : z.im≠0
  · exact contourKernel_principalPart_nonreal z hi
  have hiz : z.im=0 := not_ne_iff.mp hi
  let u : ℕ→ℂ := fun n => z+Complex.I*((1:ℂ)/((n:ℂ)+1))
  have hu : Tendsto u atTop (𝓝 z) := by
    have h := (tendsto_const_nhds (x:=Complex.I)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℂ))
    simpa [u] using (tendsto_const_nhds (x:=z)).add h
  have hkcont : ContinuousAt contourKernel z :=
    contourKernel_continuousOn.continuousAt
      (Complex.isOpen_compl_range_intCast.mem_nhds (small_nonzero_integerComplement z hz hz0))
  have hrcont : ContinuousAt (fun w : ℂ => 1/w^5+regularKernelPart w) z := by
    apply ContinuousAt.add
    · exact continuousAt_const.div (continuousAt_id.pow 5) (pow_ne_zero _ hz0)
    · exact regularKernelPart_differentiableOn.continuousOn.continuousAt
        (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball,dist_zero_right] using hz))
  apply tendsto_nhds_unique (hkcont.tendsto.comp hu)
  apply (hrcont.tendsto.comp hu).congr'
  apply Filter.Eventually.of_forall
  intro n
  apply (contourKernel_principalPart_nonreal (u n) _).symm
  have hn : (0:ℝ)<(n:ℝ)+1 := by positivity
  have him : (u n).im=1/((n:ℝ)+1) := by
    simp [u,Complex.mul_im,hiz,Complex.normSq_apply]
  rw [him]
  exact ne_of_gt (one_div_pos.mpr hn)
end OddZeta.FourValue

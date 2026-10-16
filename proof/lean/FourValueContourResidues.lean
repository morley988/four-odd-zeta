import FourValueKernelPrincipalPart
import FourValueContourConvergence

noncomputable section
namespace OddZeta.FourValue
open Polynomial Metric
open scoped Interval

theorem contourKernel_principalPart_integer (a : ℤ) (z : ℂ)
    (hz : ‖z-(a:ℂ)‖<1/2) (hz0 : z≠(a:ℂ)) :
    contourKernel z=1/(z-(a:ℂ))^5+regularKernelPart (z-(a:ℂ)) := by
  have h := contourKernel_int_period a (z-(a:ℂ))
  rw [sub_add_cancel] at h
  rw [h]
  exact contourKernel_principalPart _ hz (sub_ne_zero.mpr hz0)

theorem regularKernelPart_shift_differentiableOn (a : ℂ) (R : ℝ) (hR : R<1/2) :
    DifferentiableOn ℂ (fun z => regularKernelPart (z-a)) (closedBall a R) := by
  intro z hz
  have hball : z-a∈ball (0:ℂ) (1/2) := by
    have h := mem_closedBall.mp hz
    simpa [mem_ball,dist_zero_right,dist_eq_norm] using (h.trans_lt hR)
  exact ((regularKernelPart_differentiableOn.differentiableAt
    (isOpen_ball.mem_nhds hball)).comp z (differentiableAt_id.sub_const a)).differentiableWithinAt

theorem contourKernel_circle_residue (a : ℤ) (R : ℝ) (hR0 : 0<R) (hR1 : R<1/2)
    (F : ℂ→ℂ) (hF : DifferentiableOn ℂ F (closedBall (a:ℂ) R)) :
    (∮ z in C((a:ℂ),R),F z*contourKernel z)=
      (2*(Real.pi:ℂ)*Complex.I/24)*iteratedDeriv 4 F (a:ℂ) := by
  have hG := regularKernelPart_shift_differentiableOn (a:ℂ) R hR1
  have hFG := hF.mul hG
  have hzero : (∮ z in C((a:ℂ),R),F z*regularKernelPart (z-(a:ℂ)))=0 :=
    (hFG.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hR0.le
  have hciG : CircleIntegrable (fun z => F z*regularKernelPart (z-(a:ℂ))) (a:ℂ) R :=
    ContinuousOn.circleIntegrable hR0.le (hFG.continuousOn.mono sphere_subset_closedBall)
  have hciF : CircleIntegrable (fun z => (1/(z-(a:ℂ))^5)*F z) (a:ℂ) R := by
    apply ContinuousOn.circleIntegrable hR0.le
    apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const ((continuousOn_id.sub continuousOn_const).pow 5)
      intro z hz
      apply pow_ne_zero
      intro h
      have he : z=(a:ℂ) := sub_eq_zero.mp h
      have hd := mem_sphere.mp hz
      simp [he] at hd
      linarith
    · exact hF.continuousOn.mono sphere_subset_closedBall
  calc
    _ = ∮ z in C((a:ℂ),R),((1/(z-(a:ℂ))^5)*F z)+F z*regularKernelPart (z-(a:ℂ)) := by
      apply circleIntegral.integral_congr hR0.le
      intro z hz
      have hd : ‖z-(a:ℂ)‖=R := by simpa [dist_eq_norm] using mem_sphere.mp hz
      dsimp only
      rw [contourKernel_principalPart_integer a z (by rw [hd]; exact hR1) (by
        intro he; simp [he] at hd; linarith)]
      ring
    _ = (∮ z in C((a:ℂ),R),(1/(z-(a:ℂ))^5)*F z) := by
      rw [circleIntegral.integral_add hciF hciG,hzero,add_zero]
    _ = _ := by
      simpa [Nat.factorial,smul_eq_mul] using hF.circleIntegral_one_div_sub_center_pow_smul hR0 4

theorem analyticZetaFunction_differentiableOn (n : ℕ) (P : ℂ[X]) :
    DifferentiableOn ℂ (analyticZetaFunction n P) {z : ℂ | (67*n:ℕ)<z.re} := by
  unfold analyticZetaFunction targetZetaFunction
  exact (Polynomial.differentiable _).differentiableOn.div (Polynomial.differentiable _).differentiableOn
    (fun z hz => analyticZetaDenominator_regular_right n z hz)

theorem analyticZetaFunction_circle_residue (n t : ℕ) (P : ℂ[X]) (ht : 100*n<t) :
    (∮ z in C((t:ℂ),(1/4:ℝ)),analyticZetaFunction n P z*contourKernel z)=
      (2*(Real.pi:ℂ)*Complex.I/24)*iteratedDeriv 4 (analyticZetaFunction n P) (t:ℂ) := by
  apply contourKernel_circle_residue (t:ℤ) (1/4) (by norm_num) (by norm_num)
  apply (analyticZetaFunction_differentiableOn n P).mono
  intro z hz
  have hd : ‖z-(t:ℂ)‖≤1/4 := by simpa [dist_eq_norm] using mem_closedBall.mp hz
  have hre := Complex.abs_re_le_norm (z-(t:ℂ))
  have hsmall := (abs_le.mp (hre.trans hd)).1
  simp only [Complex.sub_re,Complex.natCast_re] at hsmall
  have ht' : ((100*n+1:ℕ):ℝ)≤t := by exact_mod_cast ht
  change ((67*n:ℕ):ℝ)<z.re
  push_cast at ht' ⊢
  have hn : (0:ℝ)≤n := by positivity
  linarith

theorem analyticZetaFunctional_residue_circle_sum (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) :
    HasSum (fun r : ℕ => ∮ z in C(((r+100*n+1:ℕ):ℂ),(1/4:ℝ)),
      analyticZetaFunction n P z*contourKernel z)
      ((2*(Real.pi:ℂ)*Complex.I)*analyticZetaFunctional n P) := by
  have h := (analyticZetaFunctional_hasSum_after_contour n P hP).mul_left (2*(Real.pi:ℂ)*Complex.I)
  apply h.congr_fun
  intro r
  rw [analyticZetaFunction_circle_residue n _ P (by omega)]
  ring
end OddZeta.FourValue

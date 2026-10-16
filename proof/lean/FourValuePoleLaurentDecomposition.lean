import FourValuePoleRegularization

noncomputable section
namespace OddZeta.FourValue
open Polynomial Set Filter Metric
open scoped Topology

def contourPoleRegularPart (F : ℂ→ℂ) (k : ℤ) (z : ℂ) : ℂ :=
  F z*regularizedContourKernel k z+iteratedPoleSlope F (k:ℂ) 5 z

theorem contourPoleRegularPart_differentiableOn (F : ℂ→ℂ) (k : ℤ)
    (hF : DifferentiableOn ℂ F (poleStrip k)) :
    DifferentiableOn ℂ (contourPoleRegularPart F k) (poleStrip k) :=
  (hF.mul (regularizedContourKernel_differentiableOn k)).add
    (iteratedPoleSlope_differentiableOn F (k:ℂ) (poleStrip k)
      ((poleStrip_isOpen k).mem_nhds (poleStrip_center_mem k)) hF 5)

theorem contourIntegrand_pole_decomposition (F : ℂ→ℂ) (k : ℤ) (z : ℂ) (hz : z≠k) :
    F z*contourKernel z=
      iteratedPoleSlope F (k:ℂ) 0 k/(z-k)^5+iteratedPoleSlope F (k:ℂ) 1 k/(z-k)^4+
      iteratedPoleSlope F (k:ℂ) 2 k/(z-k)^3+iteratedPoleSlope F (k:ℂ) 3 k/(z-k)^2+
      iteratedPoleSlope F (k:ℂ) 4 k/(z-k)+contourPoleRegularPart F k z := by
  have h := iteratedPoleSlope_div_five F (k:ℂ) z hz
  unfold contourPoleRegularPart regularizedContourKernel
  rw [if_neg hz]
  linear_combination h

theorem analyticZetaFunction_poleStrip_differentiableOn (n k : ℕ) (P : ℂ[X]) (hk : 67*n<k) :
    DifferentiableOn ℂ (analyticZetaFunction n P) (poleStrip (k:ℤ)) := by
  apply (analyticZetaFunction_differentiableOn n P).mono
  intro z hz
  have h := hz.1
  change ((67*n:ℕ):ℝ)<z.re
  have hkn : ((67*n+1:ℕ):ℝ)≤k := by exact_mod_cast hk
  push_cast at hkn h ⊢
  linarith

theorem analyticContourPoleRegularPart_differentiableOn (n k : ℕ) (P : ℂ[X]) (hk : 100*n<k) :
    DifferentiableOn ℂ (contourPoleRegularPart (analyticZetaFunction n P) (k:ℤ)) (poleStrip (k:ℤ)) :=
  contourPoleRegularPart_differentiableOn _ _ (analyticZetaFunction_poleStrip_differentiableOn n k P (by omega))

theorem poleStrip_closedBall_quarter (k : ℤ) : closedBall (k:ℂ) (1/4:ℝ) ⊆ poleStrip k := by
  intro z hz
  have hn : ‖z-(k:ℂ)‖≤1/4 := by simpa [dist_eq_norm] using mem_closedBall.mp hz
  have hr := Complex.abs_re_le_norm (z-(k:ℂ))
  have hb := abs_le.mp (hr.trans hn)
  simp only [Complex.sub_re,Complex.intCast_re] at hb
  constructor <;> linarith [hb.1,hb.2]

theorem analyticContourPoleRegularPart_circle_zero (n k : ℕ) (P : ℂ[X]) (hk : 100*n<k) :
    (∮ z in C((k:ℂ),(1/4:ℝ)),contourPoleRegularPart (analyticZetaFunction n P) (k:ℤ) z)=0 := by
  have hd := (analyticContourPoleRegularPart_differentiableOn n k P hk).mono (poleStrip_closedBall_quarter (k:ℤ))
  exact (hd.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero (by norm_num)
end OddZeta.FourValue

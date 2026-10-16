import FourValueVerticalContourIdentity
import Mathlib.Analysis.Complex.RemovableSingularity

noncomputable section
namespace OddZeta.FourValue
open Polynomial Filter Set Metric
open scoped Topology

def poleStrip (k : ℤ) : Set ℂ := {z | (k:ℝ)-3/4<z.re ∧ z.re<(k:ℝ)+3/4}

theorem poleStrip_isOpen (k : ℤ) : IsOpen (poleStrip k) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)

theorem poleStrip_center_mem (k : ℤ) : (k:ℂ)∈poleStrip k := by
  simp only [poleStrip,mem_setOf_eq,Complex.intCast_re]
  constructor <;> linarith

theorem poleStrip_noninteger_of_ne (k : ℤ) (z : ℂ) (hz : z∈poleStrip k) (hne : z≠k) :
    z∈Complex.integerComplement := by
  rintro ⟨j,hj⟩
  have hr : z.re=(j:ℝ) := by rw [← hj]; simp
  change (k:ℝ)-3/4<z.re ∧ z.re<(k:ℝ)+3/4 at hz
  have h1 : j<k+1 := by exact_mod_cast (show (j:ℝ)<(k:ℝ)+1 by rw [hr] at hz; linarith [hz.2])
  have h2 : k<j+1 := by exact_mod_cast (show (k:ℝ)<(j:ℝ)+1 by rw [hr] at hz; linarith [hz.1])
  have : j=k := by omega
  exact hne (hj.symm.trans (by rw [this]))

def regularizedContourKernel (k : ℤ) (z : ℂ) : ℂ :=
  if z=(k:ℂ) then regularKernelPart 0 else contourKernel z-1/(z-(k:ℂ))^5

theorem regularizedContourKernel_local (k : ℤ) (z : ℂ) (hz : ‖z-(k:ℂ)‖<1/2) :
    regularizedContourKernel k z=regularKernelPart (z-(k:ℂ)) := by
  by_cases he : z=(k:ℂ)
  · simp [regularizedContourKernel,he]
  · rw [regularizedContourKernel,if_neg he,contourKernel_principalPart_integer k z hz he]
    ring

theorem regularizedContourKernel_differentiableOn (k : ℤ) :
    DifferentiableOn ℂ (regularizedContourKernel k) (poleStrip k) := by
  intro z hz
  by_cases he : z=(k:ℂ)
  · subst z
    have hr : DifferentiableAt ℂ (fun z : ℂ => regularKernelPart (z-(k:ℂ))) (k:ℂ) := by
      have h0 := regularKernelPart_differentiableOn.differentiableAt
        (isOpen_ball.mem_nhds (show (0:ℂ)∈ball 0 (1/2) by simp))
      have h0' : DifferentiableAt ℂ regularKernelPart ((k:ℂ)-(k:ℂ)) := by simpa using h0
      exact h0'.comp (f:=fun z : ℂ => z-(k:ℂ)) (k:ℂ) (differentiableAt_id.sub_const (k:ℂ))
    apply DifferentiableAt.differentiableWithinAt
    apply hr.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (k:ℂ) (show (0:ℝ)<1/2 by norm_num)] with z hz
    exact (regularizedContourKernel_local k z (by simpa [dist_eq_norm] using mem_ball.mp hz))
  · have hk : DifferentiableAt ℂ contourKernel z := contourKernel_differentiableOn.differentiableAt
      (Complex.isOpen_compl_range_intCast.mem_nhds (poleStrip_noninteger_of_ne k z hz he))
    have hf : DifferentiableAt ℂ (fun z : ℂ => contourKernel z-1/(z-(k:ℂ))^5) z :=
      hk.sub ((differentiableAt_const (c:=(1:ℂ))).div ((differentiableAt_id.sub_const (k:ℂ)).pow 5) (pow_ne_zero _ (sub_ne_zero.mpr he)))
    apply DifferentiableAt.differentiableWithinAt
    apply hf.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds he] with w hw
    simp [regularizedContourKernel,hw]

def iteratedPoleSlope (F : ℂ→ℂ) (a : ℂ) : ℕ→ℂ→ℂ
  | 0 => F
  | j+1 => dslope (iteratedPoleSlope F a j) a

theorem iteratedPoleSlope_differentiableOn (F : ℂ→ℂ) (a : ℂ) (s : Set ℂ)
    (hs : s∈𝓝 a) (hF : DifferentiableOn ℂ F s) (j : ℕ) :
    DifferentiableOn ℂ (iteratedPoleSlope F a j) s := by
  induction j with
  | zero => exact hF
  | succ j ih => exact (Complex.differentiableOn_dslope hs).mpr ih

theorem iteratedPoleSlope_step (F : ℂ→ℂ) (a z : ℂ) (j : ℕ) :
    iteratedPoleSlope F a j z=iteratedPoleSlope F a j a+(z-a)*iteratedPoleSlope F a (j+1) z := by
  have h := sub_smul_dslope (iteratedPoleSlope F a j) a z
  simpa only [iteratedPoleSlope,smul_eq_mul,add_comm] using (eq_add_of_sub_eq h.symm)

theorem iteratedPoleSlope_expansion_five (F : ℂ→ℂ) (a z : ℂ) :
    F z=iteratedPoleSlope F a 0 a+(z-a)*iteratedPoleSlope F a 1 a+
      (z-a)^2*iteratedPoleSlope F a 2 a+(z-a)^3*iteratedPoleSlope F a 3 a+
      (z-a)^4*iteratedPoleSlope F a 4 a+(z-a)^5*iteratedPoleSlope F a 5 z := by
  have h0 := iteratedPoleSlope_step F a z 0
  have h1 := iteratedPoleSlope_step F a z 1
  have h2 := iteratedPoleSlope_step F a z 2
  have h3 := iteratedPoleSlope_step F a z 3
  have h4 := iteratedPoleSlope_step F a z 4
  change F z=_ at h0
  linear_combination h0+(z-a)*h1+(z-a)^2*h2+(z-a)^3*h3+(z-a)^4*h4

theorem iteratedPoleSlope_div_five (F : ℂ→ℂ) (a z : ℂ) (hz : z≠a) :
    F z/(z-a)^5=iteratedPoleSlope F a 0 a/(z-a)^5+iteratedPoleSlope F a 1 a/(z-a)^4+
      iteratedPoleSlope F a 2 a/(z-a)^3+iteratedPoleSlope F a 3 a/(z-a)^2+
      iteratedPoleSlope F a 4 a/(z-a)+iteratedPoleSlope F a 5 z := by
  have h := iteratedPoleSlope_expansion_five F a z
  rw [h]
  field_simp [sub_ne_zero.mpr hz]
  <;> ring

end OddZeta.FourValue

import FourValueRectangleLinearity

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory Set

theorem poleStrip_half_horizontal (k : ℤ) (T x : ℝ) (hx : x∈uIcc (-(1/2):ℝ) (1/2)) :
    (k:ℂ)+(x:ℂ)+(T:ℂ)*Complex.I∈poleStrip k := by
  have hb : -(1/2)≤x ∧ x≤1/2 := by
    rw [uIcc_of_le (by norm_num : (-(1/2):ℝ)≤1/2)] at hx
    exact hx
  change (k:ℝ)-3/4<((k:ℂ)+(x:ℂ)+(T:ℂ)*Complex.I).re ∧
    ((k:ℂ)+(x:ℂ)+(T:ℂ)*Complex.I).re<(k:ℝ)+3/4
  simp only [Complex.add_re,Complex.intCast_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  constructor <;> linarith [hb.1,hb.2]

theorem poleStrip_half_vertical (k : ℤ) (T : ℝ) :
    ((k:ℂ)+(1/2:ℂ)+(T:ℂ)*Complex.I)∈poleStrip k ∧
    ((k:ℂ)-(1/2:ℂ)+(T:ℂ)*Complex.I)∈poleStrip k := by
  constructor
  · simpa using poleStrip_half_horizontal k T (1/2) (by norm_num [Set.uIcc])
  · simpa [sub_eq_add_neg] using poleStrip_half_horizontal k T (-(1/2)) (by norm_num [Set.uIcc])

theorem poleRectangleIntegrable_strip (f : ℂ→ℂ) (k : ℤ) (T : ℝ)
    (hf : ContinuousOn f (poleStrip k)) : poleRectangleIntegrable f (k:ℂ) (1/2) T := by
  unfold poleRectangleIntegrable
  push_cast
  refine ⟨?_,?_,?_,?_⟩
  · apply (hf.comp (by fun_prop) ?_).intervalIntegrable
    intro x hx
    simpa [sub_eq_add_neg] using poleStrip_half_horizontal k (-T) x hx
  · exact (hf.comp (by fun_prop) (fun x hx => poleStrip_half_horizontal k T x hx)).intervalIntegrable
  · exact (hf.comp (by fun_prop) (fun x _ => (poleStrip_half_vertical k x).1)).intervalIntegrable
  · exact (hf.comp (by fun_prop) (fun x _ => (poleStrip_half_vertical k x).2)).intervalIntegrable

theorem poleRectangleBoundary_regular_zero (f : ℂ→ℂ) (k : ℤ) (T : ℝ)
    (hf : DifferentiableOn ℂ f (poleStrip k)) : poleRectangleBoundary f (k:ℂ) (1/2) T=0 := by
  have hd : DifferentiableOn ℂ (fun z : ℂ => f ((k:ℂ)+z))
      (uIcc (-(1/2):ℝ) (1/2) ×ℂ uIcc (-T) T) := by
    apply hf.comp (by fun_prop)
    intro z hz
    have hb : -(1/2)≤z.re ∧ z.re≤1/2 := by
      simpa [uIcc_of_le (show (-(1/2):ℝ)≤1/2 by norm_num)] using hz.1
    change (k:ℝ)-3/4<((k:ℂ)+z).re ∧ ((k:ℂ)+z).re<(k:ℝ)+3/4
    simp only [Complex.add_re,Complex.intCast_re]
    constructor <;> linarith [hb.1,hb.2]
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (fun z : ℂ => f ((k:ℂ)+z)) (⟨-(1/2),-T⟩:ℂ) (⟨1/2,T⟩:ℂ) hd
  simpa [poleRectangleBoundary,sub_eq_add_neg,add_assoc,neg_div] using h
end OddZeta.FourValue

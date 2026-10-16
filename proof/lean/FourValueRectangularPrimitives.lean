import FourValueRectangularPoleKernel

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory Set

theorem poleRectangleBoundary_of_primitive (f F : ℂ→ℂ) (a : ℂ) (r h : ℝ) (hr : r≠0) (hh : h≠0)
    (hF : ∀ z : ℂ,z≠a → HasDerivAt F (f z) z)
    (hc : ContinuousOn f {a}ᶜ) : poleRectangleBoundary f a r h=0 := by
  have hbne (t : ℝ) : a-(h:ℂ)*Complex.I+(t:ℂ)*1≠a := by
    intro heq
    have he : (t:ℂ)+(-h:ℂ)*Complex.I=0 := by push_cast; linear_combination heq
    exact horizontal_complex_ne_zero t (-h) (neg_ne_zero.mpr hh) (by simpa using he)
  have htne (t : ℝ) : a+(h:ℂ)*Complex.I+(t:ℂ)*1≠a := by
    intro heq
    have he : (t:ℂ)+(h:ℂ)*Complex.I=0 := by linear_combination heq
    exact horizontal_complex_ne_zero t h hh he
  have hrne (t : ℝ) : a+(r:ℂ)+(t:ℂ)*Complex.I≠a := by
    intro heq
    exact vertical_complex_ne_zero t r hr (by linear_combination heq)
  have hlne (t : ℝ) : a-(r:ℂ)+(t:ℂ)*Complex.I≠a := by
    intro heq
    have he : (-r:ℂ)+(t:ℂ)*Complex.I=0 := by push_cast; linear_combination heq
    exact vertical_complex_ne_zero t (-r) (neg_ne_zero.mpr hr) (by simpa using he)
  have hb := complex_affine_integral_primitive f F (a-(h:ℂ)*Complex.I) 1 (-r) r
    (fun t _ => hF _ (hbne t)) (hc.comp (by fun_prop) (fun t _ => hbne t))
  have ht := complex_affine_integral_primitive f F (a+(h:ℂ)*Complex.I) 1 (-r) r
    (fun t _ => hF _ (htne t)) (hc.comp (by fun_prop) (fun t _ => htne t))
  have hright := complex_affine_integral_primitive f F (a+(r:ℂ)) Complex.I (-h) h
    (fun t _ => hF _ (hrne t)) (hc.comp (by fun_prop) (fun t _ => hrne t))
  have hleft := complex_affine_integral_primitive f F (a-(r:ℂ)) Complex.I (-h) h
    (fun t _ => hF _ (hlne t)) (hc.comp (by fun_prop) (fun t _ => hlne t))
  have hbottom (x : ℝ) : a+(x:ℂ)-(h:ℂ)*Complex.I=a-(h:ℂ)*Complex.I+(x:ℂ)*1 := by ring
  have htop (x : ℝ) : a+(x:ℂ)+(h:ℂ)*Complex.I=a+(h:ℂ)*Complex.I+(x:ℂ)*1 := by ring
  unfold poleRectangleBoundary
  simp_rw [hbottom,htop]
  simp only [mul_one] at hb ht ⊢
  rw [intervalIntegral.integral_mul_const] at hright hleft
  rw [mul_comm _ Complex.I] at hright hleft
  rw [hb,ht,hright,hleft]
  push_cast
  have he1 : a-h*Complex.I+(r:ℂ)=a+(r:ℂ)+(-h)*Complex.I := by ring
  have he2 : a-(h:ℂ)*Complex.I+ -(r:ℂ)=a-(r:ℂ)+(-h)*Complex.I := by ring
  have he3 : a+(h:ℂ)*Complex.I+(r:ℂ)=a+(r:ℂ)+(h:ℂ)*Complex.I := by ring
  have he4 : a+(h:ℂ)*Complex.I+ -(r:ℂ)=a-(r:ℂ)+(h:ℂ)*Complex.I := by ring
  rw [he1,he2,he3,he4]
  ring
theorem poleRectangleBoundary_zpow (a : ℂ) (r h : ℝ) (hr : r≠0) (hh : h≠0) (m : ℤ) (hm : m≠ -1) :
    poleRectangleBoundary (fun z : ℂ => (z-a)^m) a r h=0 := by
  apply poleRectangleBoundary_of_primitive _ (fun z : ℂ => (z-a)^(m+1)/(m+1)) a r h hr hh
  · intro z hz
    convert! (((hasDerivAt_zpow (m+1) (z-a) (Or.inl (sub_ne_zero.mpr hz))).comp z
      ((hasDerivAt_id z).sub_const a)).div_const (m+1:ℂ)) using 1
    have hm' : (m+1:ℂ)≠0 := by
      exact_mod_cast (show m+1≠0 by omega)
    simp [mul_div_cancel_left₀ _ hm']
  · intro z hz
    have hne : z≠a := hz
    exact (((hasDerivAt_zpow m (z-a) (Or.inl (sub_ne_zero.mpr hne))).comp z
      ((hasDerivAt_id z).sub_const a)).continuousAt.continuousWithinAt)

end OddZeta.FourValue

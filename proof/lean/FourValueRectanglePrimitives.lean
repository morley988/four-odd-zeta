import FourValueRectangleKernel

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory Set

theorem affineComplex_hasDerivAt (z v : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => z+(t:ℂ)*v) v t := by
  convert (((hasDerivAt_id t).smul_const v).const_add z) using 1
  · rfl
  · funext x; simp [Complex.real_smul]
  · simp

theorem complex_affine_integral_primitive (f F : ℂ→ℂ) (z v : ℂ) (a b : ℝ)
    (hF : ∀ t∈Set.uIcc a b,HasDerivAt F (f (z+(t:ℂ)*v)) (z+(t:ℂ)*v))
    (hc : ContinuousOn (fun t : ℝ => f (z+(t:ℂ)*v)) (Set.uIcc a b)) :
    (∫ t in a..b,f (z+(t:ℂ)*v)*v)=F (z+(b:ℂ)*v)-F (z+(a:ℂ)*v) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    simpa only [Function.comp_def,smul_eq_mul,mul_comm] using (hF t ht).scomp t (affineComplex_hasDerivAt z v t)
  · exact (hc.mul_const v).intervalIntegrable

theorem poleSquareBoundary_of_primitive (f F : ℂ→ℂ) (a : ℂ) (r : ℝ) (hr : r≠0)
    (hF : ∀ z : ℂ,z≠a → HasDerivAt F (f z) z)
    (hc : ContinuousOn f {a}ᶜ) : poleSquareBoundary f a r=0 := by
  have hbne (t : ℝ) : a-(r:ℂ)*Complex.I+(t:ℂ)*1≠a := by
    intro h
    have he : (t:ℂ)+(-r:ℂ)*Complex.I=0 := by push_cast; linear_combination h
    exact horizontal_complex_ne_zero t (-r) (neg_ne_zero.mpr hr) (by simpa using he)
  have htne (t : ℝ) : a+(r:ℂ)*Complex.I+(t:ℂ)*1≠a := by
    intro h
    have he : (t:ℂ)+(r:ℂ)*Complex.I=0 := by linear_combination h
    exact horizontal_complex_ne_zero t r hr he
  have hrne (t : ℝ) : a+(r:ℂ)+(t:ℂ)*Complex.I≠a := by
    intro h
    exact vertical_complex_ne_zero t r hr (by linear_combination h)
  have hlne (t : ℝ) : a-(r:ℂ)+(t:ℂ)*Complex.I≠a := by
    intro h
    have he : (-r:ℂ)+(t:ℂ)*Complex.I=0 := by push_cast; linear_combination h
    exact vertical_complex_ne_zero t (-r) (neg_ne_zero.mpr hr) (by simpa using he)
  have hb := complex_affine_integral_primitive f F (a-(r:ℂ)*Complex.I) 1 (-r) r
    (fun t _ => hF _ (hbne t)) (hc.comp (by fun_prop) (fun t _ => hbne t))
  have ht := complex_affine_integral_primitive f F (a+(r:ℂ)*Complex.I) 1 (-r) r
    (fun t _ => hF _ (htne t)) (hc.comp (by fun_prop) (fun t _ => htne t))
  have hright := complex_affine_integral_primitive f F (a+(r:ℂ)) Complex.I (-r) r
    (fun t _ => hF _ (hrne t)) (hc.comp (by fun_prop) (fun t _ => hrne t))
  have hleft := complex_affine_integral_primitive f F (a-(r:ℂ)) Complex.I (-r) r
    (fun t _ => hF _ (hlne t)) (hc.comp (by fun_prop) (fun t _ => hlne t))
  have hbottom (x : ℝ) : a+(x:ℂ)-(r:ℂ)*Complex.I=a-(r:ℂ)*Complex.I+(x:ℂ)*1 := by ring
  have htop (x : ℝ) : a+(x:ℂ)+(r:ℂ)*Complex.I=a+(r:ℂ)*Complex.I+(x:ℂ)*1 := by ring
  unfold poleSquareBoundary
  simp_rw [hbottom,htop]
  simp only [mul_one] at hb ht ⊢
  rw [intervalIntegral.integral_mul_const] at hright hleft
  rw [mul_comm _ Complex.I] at hright hleft
  rw [hb,ht,hright,hleft]
  push_cast
  have he1 : a-r*Complex.I+(r:ℂ)=a+(r:ℂ)+(-r)*Complex.I := by ring
  have he2 : a-(r:ℂ)*Complex.I+ -(r:ℂ)=a-(r:ℂ)+(-r)*Complex.I := by ring
  have he3 : a+(r:ℂ)*Complex.I+(r:ℂ)=a+(r:ℂ)+(r:ℂ)*Complex.I := by ring
  have he4 : a+(r:ℂ)*Complex.I+ -(r:ℂ)=a-(r:ℂ)+(r:ℂ)*Complex.I := by ring
  rw [he1,he2,he3,he4]
  ring
theorem poleSquareBoundary_zpow (a : ℂ) (r : ℝ) (hr : r≠0) (m : ℤ) (hm : m≠ -1) :
    poleSquareBoundary (fun z : ℂ => (z-a)^m) a r=0 := by
  apply poleSquareBoundary_of_primitive _ (fun z : ℂ => (z-a)^(m+1)/(m+1)) a r hr
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

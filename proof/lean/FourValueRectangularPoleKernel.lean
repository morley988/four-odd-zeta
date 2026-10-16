import FourValueRectanglePrimitives

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory

def poleRectangleBoundary (f : ℂ→ℂ) (a : ℂ) (r h : ℝ) : ℂ :=
  (∫ x in -r..r,f (a+(x:ℂ)-(h:ℂ)*Complex.I))-
  (∫ x in -r..r,f (a+(x:ℂ)+(h:ℂ)*Complex.I))+
  Complex.I*(∫ y in -h..h,f (a+(r:ℂ)+(y:ℂ)*Complex.I))-
  Complex.I*(∫ y in -h..h,f (a-(r:ℂ)+(y:ℂ)*Complex.I))

theorem symmetric_real_kernel_integral (r c : ℝ) :
    (∫ x in -r..r,c/(c^2+x^2))=2*Real.arctan (r/c) := by
  rw [integral_div_sq_add_sq]
  simp only [neg_div,Real.arctan_neg,sub_neg_eq_add]
  ring

theorem poleRectangleBoundary_simplePole_zero (r h : ℝ) (hr : 0<r) (hh : 0<h) :
    poleRectangleBoundary (fun z : ℂ => 1/z) 0 r h=2*(Real.pi:ℂ)*Complex.I := by
  have hp : Continuous (fun x : ℝ => (1:ℂ)/((x:ℂ)+(h:ℂ)*Complex.I)) :=
    continuous_const.div (by fun_prop) (fun x => horizontal_complex_ne_zero x h hh.ne')
  have hm : Continuous (fun x : ℝ => (1:ℂ)/((x:ℂ)-(h:ℂ)*Complex.I)) := by
    apply continuous_const.div (by fun_prop)
    intro x
    simpa [sub_eq_add_neg] using horizontal_complex_ne_zero x (-h) (neg_ne_zero.mpr hh.ne')
  have vp : Continuous (fun x : ℝ => (1:ℂ)/((r:ℂ)+(x:ℂ)*Complex.I)) :=
    continuous_const.div (by fun_prop) (fun x => vertical_complex_ne_zero x r hr.ne')
  have vm : Continuous (fun x : ℝ => (1:ℂ)/(-(r:ℂ)+(x:ℂ)*Complex.I)) := by
    apply continuous_const.div (by fun_prop)
    intro x
    simpa using vertical_complex_ne_zero x (-r) (neg_ne_zero.mpr hr.ne')
  unfold poleRectangleBoundary
  simp only [zero_add,zero_sub]
  have he (A B C D : ℂ) : A-B+Complex.I*C-Complex.I*D=A-B+Complex.I*(C-D) := by ring
  rw [he,← intervalIntegral.integral_sub (hm.intervalIntegrable _ _) (hp.intervalIntegrable _ _),
    ← intervalIntegral.integral_sub (vp.intervalIntegrable _ _) (vm.intervalIntegrable _ _)]
  simp_rw [horizontal_simplePole_difference h _ hh.ne',vertical_simplePole_difference r _ hr.ne']
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal,intervalIntegral.integral_ofReal,
    symmetric_real_kernel_integral,symmetric_real_kernel_integral]
  have hs : Real.arctan (r/h)+Real.arctan (h/r)=Real.pi/2 := by
    rw [show h/r=(r/h)⁻¹ by field_simp,Real.arctan_inv_of_pos (div_pos hr hh)]
    ring
  have hs' : (Real.arctan (r/h):ℂ)+(Real.arctan (h/r):ℂ)=(Real.pi:ℂ)/2 := by exact_mod_cast hs
  push_cast
  linear_combination (4*Complex.I)*hs'

theorem poleRectangleBoundary_simplePole (a : ℂ) (r h : ℝ) (hr : 0<r) (hh : 0<h) :
    poleRectangleBoundary (fun z : ℂ => 1/(z-a)) a r h=2*(Real.pi:ℂ)*Complex.I := by
  have he : poleRectangleBoundary (fun z : ℂ => 1/(z-a)) a r h=
      poleRectangleBoundary (fun z : ℂ => 1/z) 0 r h := by
    have h1 (x y : ℂ) : (a+x-y)-a=x-y := by ring
    have h2 (x y : ℂ) : (a+x+y)-a=x+y := by ring
    have h3 (x y : ℂ) : (a-x+y)-a= -x+y := by ring
    simp only [poleRectangleBoundary,h1,h2,h3,zero_add,zero_sub]
  rw [he,poleRectangleBoundary_simplePole_zero r h hr hh]
end OddZeta.FourValue

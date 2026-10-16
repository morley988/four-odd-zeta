import FourValuePoleRegularization
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory

def poleSquareBoundary (f : ℂ→ℂ) (a : ℂ) (r : ℝ) : ℂ :=
  (∫ x in -r..r,f (a+(x:ℂ)-(r:ℂ)*Complex.I))-
  (∫ x in -r..r,f (a+(x:ℂ)+(r:ℂ)*Complex.I))+
  Complex.I*(∫ y in -r..r,f (a+(r:ℂ)+(y:ℂ)*Complex.I))-
  Complex.I*(∫ y in -r..r,f (a-(r:ℂ)+(y:ℂ)*Complex.I))

theorem horizontal_complex_ne_zero (x r : ℝ) (hr : r≠0) : (x:ℂ)+(r:ℂ)*Complex.I≠0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  exact hr hi

theorem vertical_complex_ne_zero (x r : ℝ) (hr : r≠0) : (r:ℂ)+(x:ℂ)*Complex.I≠0 := by
  intro h
  have hi := congrArg Complex.re h
  simp at hi
  exact hr hi

theorem horizontal_simplePole_difference (r x : ℝ) (hr : r≠0) :
    1/((x:ℂ)-(r:ℂ)*Complex.I)-1/((x:ℂ)+(r:ℂ)*Complex.I)=
      (2*Complex.I)*((r/(r^2+x^2):ℝ):ℂ) := by
  have h1 := horizontal_complex_ne_zero x r hr
  have h2 : (x:ℂ)-(r:ℂ)*Complex.I≠0 := by
    simpa [sub_eq_add_neg] using horizontal_complex_ne_zero x (-r) (neg_ne_zero.mpr hr)
  have hd : ((r:ℂ)^2+(x:ℂ)^2)≠0 := by
    exact_mod_cast (show r^2+x^2≠0 by nlinarith [sq_pos_of_ne_zero hr,sq_nonneg x])
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]
  <;> ring

theorem vertical_simplePole_difference (r x : ℝ) (hr : r≠0) :
    1/((r:ℂ)+(x:ℂ)*Complex.I)-1/(-(r:ℂ)+(x:ℂ)*Complex.I)=
      2*((r/(r^2+x^2):ℝ):ℂ) := by
  have h1 := vertical_complex_ne_zero x r hr
  have h2 := vertical_complex_ne_zero x (-r) (neg_ne_zero.mpr hr)
  have hd : ((r:ℂ)^2+(x:ℂ)^2)≠0 := by
    exact_mod_cast (show r^2+x^2≠0 by nlinarith [sq_pos_of_ne_zero hr,sq_nonneg x])
  push_cast at h2 ⊢
  field_simp
  ring_nf
  simp [Complex.I_sq]
  <;> ring

theorem square_real_kernel_integral (r : ℝ) (hr : r≠0) :
    (∫ x in -r..r,r/(r^2+x^2))=Real.pi/2 := by
  rw [integral_div_sq_add_sq]
  simp [hr,Real.arctan_one]
  ring

theorem poleSquareBoundary_simplePole_zero (r : ℝ) (hr : r≠0) :
    poleSquareBoundary (fun z : ℂ => 1/z) 0 r=2*(Real.pi:ℂ)*Complex.I := by
  have hp : Continuous (fun x : ℝ => (1:ℂ)/((x:ℂ)+(r:ℂ)*Complex.I)) :=
    continuous_const.div (by fun_prop) (fun x => horizontal_complex_ne_zero x r hr)
  have hm : Continuous (fun x : ℝ => (1:ℂ)/((x:ℂ)-(r:ℂ)*Complex.I)) := by
    apply continuous_const.div (by fun_prop)
    intro x
    simpa [sub_eq_add_neg] using horizontal_complex_ne_zero x (-r) (neg_ne_zero.mpr hr)
  have vp : Continuous (fun x : ℝ => (1:ℂ)/((r:ℂ)+(x:ℂ)*Complex.I)) :=
    continuous_const.div (by fun_prop) (fun x => vertical_complex_ne_zero x r hr)
  have vm : Continuous (fun x : ℝ => (1:ℂ)/(-(r:ℂ)+(x:ℂ)*Complex.I)) := by
    apply continuous_const.div (by fun_prop)
    intro x
    simpa using vertical_complex_ne_zero x (-r) (neg_ne_zero.mpr hr)
  unfold poleSquareBoundary
  simp only [zero_add,zero_sub]
  have he (A B C D : ℂ) : A-B+Complex.I*C-Complex.I*D=A-B+Complex.I*(C-D) := by ring
  rw [he,← intervalIntegral.integral_sub (hm.intervalIntegrable _ _) (hp.intervalIntegrable _ _),
    ← intervalIntegral.integral_sub (vp.intervalIntegrable _ _) (vm.intervalIntegrable _ _)]
  simp_rw [horizontal_simplePole_difference r _ hr,vertical_simplePole_difference r _ hr]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal,square_real_kernel_integral r hr]
  push_cast
  ring

theorem poleSquareBoundary_simplePole (a : ℂ) (r : ℝ) (hr : r≠0) :
    poleSquareBoundary (fun z : ℂ => 1/(z-a)) a r=2*(Real.pi:ℂ)*Complex.I := by
  have he : poleSquareBoundary (fun z : ℂ => 1/(z-a)) a r=
      poleSquareBoundary (fun z : ℂ => 1/z) 0 r := by
    have h1 (x y : ℂ) : (a+x-y)-a=x-y := by ring
    have h2 (x y : ℂ) : (a+x+y)-a=x+y := by ring
    have h3 (x y : ℂ) : (a-x+y)-a= -x+y := by ring
    simp only [poleSquareBoundary,h1,h2,h3,zero_add,zero_sub]
  rw [he,poleSquareBoundary_simplePole_zero r hr]

end OddZeta.FourValue

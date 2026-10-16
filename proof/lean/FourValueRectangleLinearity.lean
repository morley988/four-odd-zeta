import FourValueRectangularPrimitives
import FourValuePoleResidueCoefficient

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory Set

def poleRectangleIntegrable (f : ℂ→ℂ) (a : ℂ) (r h : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f (a+(x:ℂ)-(h:ℂ)*Complex.I)) volume (-r) r ∧
  IntervalIntegrable (fun x : ℝ => f (a+(x:ℂ)+(h:ℂ)*Complex.I)) volume (-r) r ∧
  IntervalIntegrable (fun y : ℝ => f (a+(r:ℂ)+(y:ℂ)*Complex.I)) volume (-h) h ∧
  IntervalIntegrable (fun y : ℝ => f (a-(r:ℂ)+(y:ℂ)*Complex.I)) volume (-h) h

theorem poleRectangleIntegrable_add (f g : ℂ→ℂ) (a : ℂ) (r h : ℝ)
    (hf : poleRectangleIntegrable f a r h) (hg : poleRectangleIntegrable g a r h) :
    poleRectangleIntegrable (fun z => f z+g z) a r h :=
  ⟨hf.1.add hg.1,hf.2.1.add hg.2.1,hf.2.2.1.add hg.2.2.1,hf.2.2.2.add hg.2.2.2⟩

theorem poleRectangleIntegrable_const_mul (c : ℂ) (f : ℂ→ℂ) (a : ℂ) (r h : ℝ)
    (hf : poleRectangleIntegrable f a r h) : poleRectangleIntegrable (fun z => c*f z) a r h :=
  ⟨hf.1.const_mul c,hf.2.1.const_mul c,hf.2.2.1.const_mul c,hf.2.2.2.const_mul c⟩

theorem poleRectangleBoundary_add (f g : ℂ→ℂ) (a : ℂ) (r h : ℝ)
    (hf : poleRectangleIntegrable f a r h) (hg : poleRectangleIntegrable g a r h) :
    poleRectangleBoundary (fun z => f z+g z) a r h=poleRectangleBoundary f a r h+poleRectangleBoundary g a r h := by
  unfold poleRectangleBoundary
  rw [intervalIntegral.integral_add hf.1 hg.1,intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

theorem poleRectangleBoundary_const_mul (c : ℂ) (f : ℂ→ℂ) (a : ℂ) (r h : ℝ) :
    poleRectangleBoundary (fun z => c*f z) a r h=c*poleRectangleBoundary f a r h := by
  unfold poleRectangleBoundary
  simp only [intervalIntegral.integral_const_mul]
  ring

theorem poleRectangleBoundary_congr (f g : ℂ→ℂ) (a : ℂ) (r h : ℝ)
    (h1 : ∀ x∈uIcc (-r) r,f (a+(x:ℂ)-(h:ℂ)*Complex.I)=g (a+(x:ℂ)-(h:ℂ)*Complex.I))
    (h2 : ∀ x∈uIcc (-r) r,f (a+(x:ℂ)+(h:ℂ)*Complex.I)=g (a+(x:ℂ)+(h:ℂ)*Complex.I))
    (h3 : ∀ y∈uIcc (-h) h,f (a+(r:ℂ)+(y:ℂ)*Complex.I)=g (a+(r:ℂ)+(y:ℂ)*Complex.I))
    (h4 : ∀ y∈uIcc (-h) h,f (a-(r:ℂ)+(y:ℂ)*Complex.I)=g (a-(r:ℂ)+(y:ℂ)*Complex.I)) :
    poleRectangleBoundary f a r h=poleRectangleBoundary g a r h := by
  unfold poleRectangleBoundary
  rw [intervalIntegral.integral_congr h1,intervalIntegral.integral_congr h2,
    intervalIntegral.integral_congr h3,intervalIntegral.integral_congr h4]

theorem poleRectangle_edges_ne (a : ℂ) (r h : ℝ) (hr : r≠0) (hh : h≠0) :
    (∀ x : ℝ,a+(x:ℂ)-(h:ℂ)*Complex.I≠a) ∧ (∀ x : ℝ,a+(x:ℂ)+(h:ℂ)*Complex.I≠a) ∧
    (∀ y : ℝ,a+(r:ℂ)+(y:ℂ)*Complex.I≠a) ∧ (∀ y : ℝ,a-(r:ℂ)+(y:ℂ)*Complex.I≠a) := by
  constructor
  · intro x he
    apply horizontal_complex_ne_zero x (-h) (neg_ne_zero.mpr hh)
    push_cast
    linear_combination he
  constructor
  · intro x he
    apply horizontal_complex_ne_zero x h hh
    linear_combination he
  constructor
  · intro y he
    apply vertical_complex_ne_zero y r hr
    linear_combination he
  · intro y he
    apply vertical_complex_ne_zero y (-r) (neg_ne_zero.mpr hr)
    push_cast
    linear_combination he

theorem poleRectangleIntegrable_punctured (f : ℂ→ℂ) (a : ℂ) (r h : ℝ)
    (hr : r≠0) (hh : h≠0) (hf : ContinuousOn f {a}ᶜ) : poleRectangleIntegrable f a r h := by
  obtain ⟨h1,h2,h3,h4⟩ := poleRectangle_edges_ne a r h hr hh
  exact ⟨(hf.comp (by fun_prop) (fun x _ => h1 x)).intervalIntegrable,
    (hf.comp (by fun_prop) (fun x _ => h2 x)).intervalIntegrable,
    (hf.comp (by fun_prop) (fun x _ => h3 x)).intervalIntegrable,
    (hf.comp (by fun_prop) (fun x _ => h4 x)).intervalIntegrable⟩

theorem poleRectangleIntegrable_zpow (a : ℂ) (r h : ℝ) (hr : r≠0) (hh : h≠0) (m : ℤ) :
    poleRectangleIntegrable (fun z : ℂ => (z-a)^m) a r h := by
  apply poleRectangleIntegrable_punctured _ a r h hr hh
  intro z hz
  have hne : z≠a := hz
  exact (((hasDerivAt_zpow m (z-a) (Or.inl (sub_ne_zero.mpr hne))).comp z
    ((hasDerivAt_id z).sub_const a)).continuousAt.continuousWithinAt)
end OddZeta.FourValue

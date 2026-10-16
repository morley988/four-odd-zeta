import FourValueZetaIdentity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
namespace OddZeta.FourValue
open Polynomial Filter
open scoped Topology

def poleTaylorValue (a : ℂ) (k h : ℕ) (x : ℂ) : ℂ :=
  (-1:ℂ)^h*(Nat.choose (k+h) h:ℂ)/(x-a)^(k+h+1)

theorem poleTaylorValue_hasDerivAt (a x : ℂ) (hx : x≠a) (k h : ℕ) :
    HasDerivAt (poleTaylorValue a k h)
      ((h+1:ℕ)*poleTaylorValue a k (h+1) x) x := by
  have H := (((hasDerivAt_id x).sub_const a).pow (k+h+1)).inv
    (pow_ne_zero _ (sub_ne_zero.mpr hx))
  have H' := H.const_mul ((-1:ℂ)^h*(Nat.choose (k+h) h:ℂ))
  have hchoose : ((k+h+1:ℕ):ℂ)*(Nat.choose (k+h) h:ℂ)=
      (Nat.choose (k+h+1) (h+1):ℂ)*((h+1:ℕ):ℂ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq (k+h) h
  convert H' using 1 <;> try rfl
  simp only [poleTaylorValue, Nat.add_sub_cancel, id_eq, Pi.pow_apply, Pi.sub_apply,
    Pi.one_apply, mul_one]
  have hn : k+(h+1)+1=(k+h+1)+1 := by omega
  rw [hn,pow_succ,pow_succ]
  field_simp [sub_ne_zero.mpr hx]
  linear_combination (x-a)^(k+h+1)*hchoose

def partialFractionValue (b : ℕ) (c : ℤ → Fin 10 → ℂ) (h : ℕ) (x : ℂ) : ℂ :=
  ∑ j ∈ poleWindow b,∑ k : Fin 10,c j k*poleTaylorValue (j:ℂ) k.val h x

def OutsidePoleWindow (b : ℕ) (c : ℤ → Fin 10 → ℂ) (x : ℂ) : Prop :=
  ∀ j∈poleWindow b,∀ k,c j k=0 ∨ x≠(j:ℂ)

theorem outsidePoleWindow_eventually (b : ℕ) (c : ℤ → Fin 10 → ℂ) (x : ℂ) (hx : OutsidePoleWindow b c x) :
    ∀ᶠ y in 𝓝 x, OutsidePoleWindow b c y := by
  simp only [OutsidePoleWindow]
  apply (Filter.eventually_all_finite (poleWindow b).finite_toSet).mpr
  intro j hj
  apply Filter.eventually_all.mpr
  intro k
  rcases hx j hj k with hz | hne
  · exact Filter.Eventually.of_forall (fun y => Or.inl hz)
  · filter_upwards [eventually_ne_nhds hne] with y hy
    exact Or.inr hy

theorem partialFractionValue_hasDerivAt (b : ℕ) (c : ℤ → Fin 10 → ℂ) (h : ℕ)
    (x : ℂ) (hx : OutsidePoleWindow b c x) :
    HasDerivAt (partialFractionValue b c h)
      ((h+1:ℕ)*partialFractionValue b c (h+1) x) x := by
  have hterm (j : ℤ) (hj : j∈poleWindow b) (k : Fin 10) :
      HasDerivAt (fun y => c j k*poleTaylorValue (j:ℂ) k.val h y)
        (c j k*((h+1:ℕ)*poleTaylorValue (j:ℂ) k.val (h+1) x)) x := by
    rcases hx j hj k with hz | hne
    · simpa [hz] using hasDerivAt_const x (0:ℂ)
    · exact (poleTaylorValue_hasDerivAt (j:ℂ) x hne k.val h).const_mul (c j k)
  have H := HasDerivAt.sum (u:=poleWindow b) (fun j hj =>
    HasDerivAt.sum (u:=Finset.univ) (fun k _ => hterm j hj k))
  convert H using 1 <;> try rfl
  · funext y; simp [partialFractionValue]
  · simp only [partialFractionValue,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring

theorem partialFractionValue_iteratedDeriv (b : ℕ) (c : ℤ → Fin 10 → ℂ)
    (h : ℕ) (x : ℂ) (hx : OutsidePoleWindow b c x) :
    iteratedDeriv h (partialFractionValue b c 0) x =
      (Nat.factorial h:ℂ)*partialFractionValue b c h x := by
  induction h generalizing x with
  | zero => simp
  | succ h ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv h (partialFractionValue b c 0) =ᶠ[𝓝 x]
        (fun y => (Nat.factorial h:ℂ)*partialFractionValue b c h y) := by
      filter_upwards [outsidePoleWindow_eventually b c x hx] with y hy
      exact ih y hy
    rw [heq.deriv_eq]
    rw [((partialFractionValue_hasDerivAt b c h x hx).const_mul (Nat.factorial h:ℂ)).deriv]
    simp only [Nat.factorial_succ,Nat.cast_mul]
    ring

theorem rationalCoefficientAt_partialFraction_regular (b h : ℕ)
    (f : RatFunc ℂ) (c : ℤ → Fin 10 → ℂ)
    (hf : f=∑ j ∈ poleWindow b,∑ k : Fin 10,c j k • rationalPole (j:ℂ) (k.val+1))
    (x : ℂ) (hx : OutsidePoleWindow b c x) :
    rationalCoefficientAt x h f=partialFractionValue b c h x := by
  rw [hf]
  simp only [map_sum,map_smul,smul_eq_mul,partialFractionValue]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rcases hx j hj k with hz | hne
  · simp [hz]
  · rw [rationalCoefficientAt_pole_regular _ _ hne]
    rfl

end OddZeta.FourValue

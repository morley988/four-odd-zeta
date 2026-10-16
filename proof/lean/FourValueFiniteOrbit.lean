import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

/-!
Finite-dimensional propagation used in the Pearson nonvanishing argument.
These are unconditional linear-algebra lemmas.  Constructing the quotient
representation of the actual Pearson functional is a separate obligation.
-/

namespace OddZeta.FourValue
open Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A linear observation of a polynomial in an endomorphism is the matching
finite linear combination of observations of its powers. -/
theorem observe_aeval (T : Module.End K V) (v : V) (L : V →ₗ[K] K)
    (p : K[X]) :
    L ((aeval T p) v) =
      ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * L ((T ^ j) v) := by
  rw [Polynomial.aeval_eq_sum_range]
  simp [LinearMap.sum_apply]

/-- Cayley--Hamilton: vanishing through dimension minus one propagates to
every power. This includes zero-dimensional spaces. -/
theorem observe_powers_zero [FiniteDimensional K V]
    (T : Module.End K V) (v : V) (L : V →ₗ[K] K)
    (h : ∀ j < Module.finrank K V, L ((T ^ j) v) = 0) :
    ∀ j : ℕ, L ((T ^ j) v) = 0 := by
  intro j
  by_cases hd : Module.finrank K V = 0
  · have : Subsingleton V := (Module.finrank_zero_iff).mp hd
    have hv : (T ^ j) v = 0 := Subsingleton.elim _ _
    simp [hv]
  · rw [T.pow_eq_aeval_mod_charpoly j, observe_aeval]
    apply Finset.sum_eq_zero
    intro i hi
    have hcp : T.charpoly ≠ 1 := by
      intro heq
      have heq' := T.charpoly_natDegree
      rw [heq, Polynomial.natDegree_one] at heq'
      exact hd heq'.symm
    have hdeg := Polynomial.natDegree_modByMonic_lt (X ^ j) T.charpoly_monic hcp
    rw [T.charpoly_natDegree] at hdeg
    have hi' : i < Module.finrank K V := by
      have := Finset.mem_range.mp hi
      omega
    simp [h i hi']

/-- The same finite check suffices for every polynomial, not just powers. -/
theorem observe_all_polynomials_zero [FiniteDimensional K V]
    (T : Module.End K V) (v : V) (L : V →ₗ[K] K)
    (h : ∀ j < Module.finrank K V, L ((T ^ j) v) = 0) :
    ∀ p : K[X], L ((aeval T p) v) = 0 := by
  intro p
  rw [observe_aeval]
  apply Finset.sum_eq_zero
  intro i _
  simp [observe_powers_zero T v L h i]

end OddZeta.FourValue

import FourValuePearsonBridge
import FourValueMinorSelection
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
The original conditional assembly of uniform Hankel nonvanishing.
FourValueHankelExtension now proves the short-annihilator hypothesis and
provides hankel_rank_bound_of_finite_exclusion. The classified initial
vectors and their independence still require family-specific verification.
These hypotheses are visible arguments, not axioms or hidden instances.
-/

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def momentHankel (L : K[X] →ₗ[K] K) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  fun i j => L (X ^ (i.val + j.val))

def HasShortAnnihilator (L : K[X] →ₗ[K] K) (m r : ℕ) : Prop :=
  ∃ p : K[X], p.Monic ∧ p.natDegree ≤ r ∧
    ∀ j ≤ 2 * m - r, L (p * X ^ j) = 0

def initialMoments (L : K[X] →ₗ[K] K) : Fin 9 → K :=
  fun j => L (X ^ j.val)

def liftedInitialMoments (U : K[X] →ₗ[K] K) : Fin 9 → K :=
  fun j => U (X * expand K 2 (X ^ j.val))

/-- The algebraic part of the rank argument, with the apolar and
classification hypotheses kept explicit. -/
theorem hankel_rank_bound_of_short_annihilators
    (L : K[X] →ₗ[K] K) (A : K[X]) (m : ℕ)
    (hA : A.natDegree ≤ 20)
    (hrel : ∀ j : ℕ, j + 9 ≤ 2 * m → L (pearsonOperator A (X ^ j)) = 0)
    (hapolar : ∀ r ≤ m, (momentHankel L m).rank ≤ r → HasShortAnnihilator L m r)
    (hexclusion : ∀ U : K[X] →ₗ[K] K, IsFinitePearson A U →
      liftedInitialMoments U ≠ initialMoments L) :
    m + 1 - 4 ≤ (momentHankel L m).rank := by
  apply rank_at_least
  intro hr
  let r := (momentHankel L m).rank
  obtain ⟨p, hp, hs, hann⟩ := hapolar r (by dsimp [r]; omega) (le_refl _)
  have hfinite := recurrenceExtension_isFinitePearson L A hA hp m r hs hr hann hrel
  apply hexclusion (oddLift (recurrenceExtension L p)) hfinite
  funext j
  exact finitePearson_initial_agreement L hp m r hs hr hann j.val (by omega)

/-- Independence excludes a nonzero final coordinate from every classified
finite initial vector whose final coordinate is zero. -/
theorem initial_coordinate_exclusion
    (L : K[X] →ₗ[K] K) (A : K[X]) (v : Fin 9 → (Fin 9 → K))
    (hv : LinearIndependent K v) (a : Fin 9 → K) (ha : a 8 ≠ 0)
    (hL : initialMoments L = ∑ i, a i • v i)
    (hclass : ∀ U : K[X] →ₗ[K] K, IsFinitePearson A U →
      ∃ b : Fin 9 → K, b 8 = 0 ∧ liftedInitialMoments U = ∑ i, b i • v i) :
    ∀ U : K[X] →ₗ[K] K, IsFinitePearson A U →
      liftedInitialMoments U ≠ initialMoments L := by
  intro U hU heq
  obtain ⟨b, hb, hUb⟩ := hclass U hU
  have hsum : ∑ i, a i • v i = ∑ i, b i • v i := by
    rw [← hL, ← hUb, heq]
  have hab := hv.eq_coords_of_eq hsum 8
  exact ha (hab.trans hb)

/-- Conditional nonvanishing of an actual almost-full minor, using the
general matrix selection theorem proved separately in this project. -/
theorem hankel_nonzero_minor_of_short_annihilators
    (L : K[X] →ₗ[K] K) (A : K[X]) (m : ℕ)
    (hA : A.natDegree ≤ 20)
    (hrel : ∀ j : ℕ, j + 9 ≤ 2 * m → L (pearsonOperator A (X ^ j)) = 0)
    (hapolar : ∀ r ≤ m, (momentHankel L m).rank ≤ r → HasShortAnnihilator L m r)
    (hexclusion : ∀ U : K[X] →ₗ[K] K, IsFinitePearson A U →
      liftedInitialMoments U ≠ initialMoments L) :
    ∃ rows cols : Fin (m + 1 - 4) ↪ Fin (m + 1),
      ((momentHankel L m).submatrix rows cols).det ≠ 0 :=
  rank_selects_nonzero_minor _
    (hankel_rank_bound_of_short_annihilators L A m hA hrel hapolar hexclusion)

end OddZeta.FourValue

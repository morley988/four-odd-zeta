import FourValueFiniteOrbit
import FourValueOddLift
import Mathlib.RingTheory.AdjoinRoot

/-! A functional annihilated by a polynomial factors through its actual
finite quotient. Cayley--Hamilton then propagates Pearson-type tests. -/

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K]

def quotientObservation (L : K[X] →ₗ[K] K) {p : K[X]} (hp : p.Monic) :
    AdjoinRoot p →ₗ[K] K := L.comp (AdjoinRoot.modByMonicHom hp)

theorem quotientObservation_mk (L : K[X] →ₗ[K] K) {p : K[X]} (hp : p.Monic)
    (hann : ∀ q : K[X], L (p * q) = 0) (f : K[X]) :
    quotientObservation L hp (AdjoinRoot.mk p f) = L f := by
  change L (f %ₘ p) = L f
  have heq := congrArg L (Polynomial.modByMonic_add_div f p)
  simpa [map_add, hann] using heq

/-- Testing `A*q^j` through dimension minus one suffices for every `j`.
The quotient is `K[X]/(p)` itself, not an assumed finite representation. -/
theorem annihilator_propagates_tests (L : K[X] →ₗ[K] K) {p : K[X]}
    (hp : p.Monic) (hann : ∀ f : K[X], L (p * f) = 0)
    (A q : K[X]) (h : ∀ j < p.natDegree, L (A * q ^ j) = 0) :
    ∀ j : ℕ, L (A * q ^ j) = 0 := by
  let := hp.finite_adjoinRoot
  let T : Module.End K (AdjoinRoot p) :=
    Algebra.lmul K (AdjoinRoot p) (AdjoinRoot.mk p q)
  let v : AdjoinRoot p := AdjoinRoot.mk p A
  let obs : AdjoinRoot p →ₗ[K] K := quotientObservation L hp
  have hdim : Module.finrank K (AdjoinRoot p) = p.natDegree := by
    exact (AdjoinRoot.powerBasis' hp).finrank
  have hformula (j : ℕ) : obs ((T ^ j) v) = L (A * q ^ j) := by
    change quotientObservation L hp
      (((Algebra.lmul K (AdjoinRoot p) (AdjoinRoot.mk p q)) ^ j)
        (AdjoinRoot.mk p A)) = _
    rw [← map_pow]
    change quotientObservation L hp
      ((AdjoinRoot.mk p q) ^ j * AdjoinRoot.mk p A) = _
    rw [← map_pow, ← map_mul, quotientObservation_mk L hp hann, mul_comm]
  have hzero : ∀ j < Module.finrank K (AdjoinRoot p), obs ((T ^ j) v) = 0 := by
    intro j hj
    rw [hformula]
    exact h j (by simpa [hdim] using hj)
  intro j
  rw [← hformula]
  exact observe_powers_zero T v obs hzero j

/-- Applied to the squared-coordinate lift, exactly twice `degree p`
tests suffice. The test polynomial may in particular be `(X+1)^2`. -/
theorem oddLift_propagates_tests (L : K[X] →ₗ[K] K) {p : K[X]}
    (hp : p.Monic) (hann : ∀ f : K[X], L (p * f) = 0)
    (A q : K[X])
    (h : ∀ j < 2 * p.natDegree, oddLift L (A * q ^ j) = 0) :
    ∀ j : ℕ, oddLift L (A * q ^ j) = 0 := by
  apply annihilator_propagates_tests (oddLift L)
    (hp.expand (by decide : 0 < 2)) (oddLift_annihilator L p hann) A q
  intro j hj
  apply h j
  simpa [Polynomial.natDegree_expand, mul_comm] using hj

end OddZeta.FourValue

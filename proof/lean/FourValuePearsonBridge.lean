import FourValueRecurrence
import FourValueFiniteQuotient
import FourValuePearsonOperator

/-!
The central algebraic bridge in the uniform nonvanishing proof: a short
truncated annihilator and the available difference relations produce an
actual finite odd Pearson functional agreeing on the initial moments.
The short annihilator is proved in FourValueHankelExtension. The support
and seven-dimensional upper bound are proved in FourValueFiniteDimension;
the family-specific first-nine-moment restriction remains to be identified.
-/

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def pearsonTestMap (A : K[X]) (U : K[X] →ₗ[K] K) : K[X] →ₗ[K] K where
  toFun q := U (A * q.comp ((X + 1) ^ 2))
  map_add' f g := by simp [Polynomial.add_comp, mul_add]
  map_smul' a f := by simp [Polynomial.smul_comp]

omit [CharZero K] in
theorem linearFunctional_zero_of_powers (L : K[X] →ₗ[K] K)
    (h : ∀ j : ℕ, L (X ^ j) = 0) : L = 0 := by
  apply LinearMap.ext
  intro q
  rw [q.as_sum_range_C_mul_X_pow, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [← Polynomial.smul_eq_C_mul, map_smul, h j, smul_zero]

/-- A finite odd solution of the Pearson relation, stated without reference
to jets or support classification. -/
def IsFinitePearson (A : K[X]) (U : K[X] →ₗ[K] K) : Prop :=
  (∃ p : K[X], p ≠ 0 ∧ ∀ f : K[X], U (p * f) = 0) ∧
  (∀ f : K[X], U (f.comp (-X)) = -U f) ∧
  ∀ q : K[X], U (A * q.comp ((X + 1) ^ 2)) = 0

/-- The low-degree Pearson relations transfer to the recurrence extension
for every test needed by the dimension bound. -/
theorem recurrenceExtension_pearson_tests
    (L : K[X] →ₗ[K] K) (A : K[X]) (hA : A.natDegree ≤ 20)
    {p : K[X]} (hp : p.Monic) (m r : ℕ)
    (hs : p.natDegree ≤ r) (hr : r + 4 ≤ m)
    (hann : ∀ j ≤ 2 * m - r, L (p * X ^ j) = 0)
    (hrel : ∀ j : ℕ, j + 9 ≤ 2 * m → L (pearsonOperator A (X ^ j)) = 0) :
    ∀ j < 2 * p.natDegree,
      oddLift (recurrenceExtension L p) (A * ((X + 1) ^ 2) ^ j) = 0 := by
  intro j hj
  apply pearsonOperator_test_zero
  rw [recurrenceExtension_agrees L hp (2 * m - r) hann]
  · apply hrel j
    omega
  · have hd := pearsonOperator_monomial_degree A hA j
    omega

theorem recurrenceExtension_isFinitePearson
    (L : K[X] →ₗ[K] K) (A : K[X]) (hA : A.natDegree ≤ 20)
    {p : K[X]} (hp : p.Monic) (m r : ℕ)
    (hs : p.natDegree ≤ r) (hr : r + 4 ≤ m)
    (hann : ∀ j ≤ 2 * m - r, L (p * X ^ j) = 0)
    (hrel : ∀ j : ℕ, j + 9 ≤ 2 * m → L (pearsonOperator A (X ^ j)) = 0) :
    IsFinitePearson A (oddLift (recurrenceExtension L p)) := by
  have hfinite := recurrenceExtension_annihilates L hp
  refine ⟨⟨expand K 2 p, (hp.expand (by decide : 0 < 2)).ne_zero,
    oddLift_annihilator _ p hfinite⟩, oddLift_reflect _, ?_⟩
  have hinit := recurrenceExtension_pearson_tests L A hA hp m r hs hr hann hrel
  have hall := oddLift_propagates_tests (recurrenceExtension L p) hp hfinite
    A ((X + 1) ^ 2) hinit
  have hmap : pearsonTestMap A (oddLift (recurrenceExtension L p)) = 0 := by
    apply linearFunctional_zero_of_powers
    intro j
    simpa [pearsonTestMap] using hall j
  intro q
  exact LinearMap.congr_fun hmap q

omit [CharZero K] in
/-- All initial moments needed by the nine-dimensional independence test
are preserved by the constructed finite Pearson functional. -/
theorem finitePearson_initial_agreement
    (L : K[X] →ₗ[K] K) {p : K[X]} (hp : p.Monic) (m r : ℕ)
    (_hs : p.natDegree ≤ r) (hr : r + 4 ≤ m)
    (hann : ∀ j ≤ 2 * m - r, L (p * X ^ j) = 0) :
    ∀ j ≤ 8,
      oddLift (recurrenceExtension L p) (X * expand K 2 (X ^ j)) = L (X ^ j) := by
  intro j hj
  rw [oddLift_X_expand]
  apply recurrenceExtension_agrees L hp (2 * m - r) hann
  simp only [Polynomial.natDegree_X_pow]
  omega

end OddZeta.FourValue

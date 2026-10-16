import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic

/-!
The constructive extension step of the truncated Hankel lemma. A short
annihilating polynomial is an explicit hypothesis here; existence of that
polynomial from a rank defect is the separate apolarity obligation.
-/

noncomputable section
namespace OddZeta.FourValue
open Polynomial

variable {K : Type*} [Field K]

/-- Extend a truncated recurrence by first reducing every test polynomial
modulo its monic annihilator. -/
def recurrenceExtension (L : K[X] →ₗ[K] K) (p : K[X]) : K[X] →ₗ[K] K :=
  L.comp (Polynomial.modByMonicHom p)

@[simp] theorem recurrenceExtension_apply (L : K[X] →ₗ[K] K) (p q : K[X]) :
    recurrenceExtension L p q = L (q %ₘ p) := rfl

/-- The extended functional is annihilated on every multiple of `p`. -/
theorem recurrenceExtension_annihilates (L : K[X] →ₗ[K] K)
    {p : K[X]} (hp : p.Monic) (q : K[X]) :
    recurrenceExtension L p (p * q) = 0 := by
  rw [recurrenceExtension_apply, (Polynomial.modByMonic_eq_zero_iff_dvd hp).2
    (dvd_mul_right p q), map_zero]

/-- Monomial recurrence relations imply all relations in the same degree
range by linearity. -/
theorem recurrence_relations_span (L : K[X] →ₗ[K] K) (p : K[X]) (b : ℕ)
    (h : ∀ j ≤ b, L (p * X ^ j) = 0) (q : K[X])
    (hq : q.natDegree ≤ b) : L (p * q) = 0 := by
  conv_lhs => rw [q.as_sum_range_C_mul_X_pow]
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i ≤ b := by
    have := Finset.mem_range.mp hi
    omega
  rw [show p * (C (q.coeff i) * X ^ i) =
    q.coeff i • (p * X ^ i) by simp [Polynomial.smul_eq_C_mul, mul_left_comm]]
  simp [h i hi']

/-- Agreement extends through `b + degree p`, including a degree-zero
annihilator. This accounts for the root-at-infinity degree loss. -/
theorem recurrenceExtension_agrees (L : K[X] →ₗ[K] K)
    {p : K[X]} (hp : p.Monic) (b : ℕ)
    (h : ∀ j ≤ b, L (p * X ^ j) = 0) (q : K[X])
    (hq : q.natDegree ≤ b + p.natDegree) :
    recurrenceExtension L p q = L q := by
  have hdiv : (q /ₘ p).natDegree ≤ b := by
    rw [Polynomial.natDegree_divByMonic q hp]
    omega
  have hz := recurrence_relations_span L p b h (q /ₘ p) hdiv
  have heq := congrArg L (Polynomial.modByMonic_add_div q p)
  simpa [recurrenceExtension_apply, map_add, hz] using heq

/-- The exact degree of agreement appearing in the paper's apolar extension. -/
theorem recurrenceExtension_hankel_agrees (L : K[X] →ₗ[K] K)
    {p : K[X]} (hp : p.Monic) (m r : ℕ)
    (h : ∀ j ≤ 2 * m - r, L (p * X ^ j) = 0)
    (q : K[X]) (hq : q.natDegree ≤ 2 * m - r + p.natDegree) :
    recurrenceExtension L p q = L q :=
  recurrenceExtension_agrees L hp (2 * m - r) h q hq

/-- For a degree-zero monic annihilator the extension is the zero functional. -/
theorem recurrenceExtension_one (L : K[X] →ₗ[K] K) :
    recurrenceExtension L (1 : K[X]) = 0 := by
  ext q
  simp [recurrenceExtension_apply]

end OddZeta.FourValue

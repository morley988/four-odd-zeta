import FourValuePearsonBridge
import Mathlib.Tactic

/-! The Pearson test equation is exactly an affine reflection identity.
This is the algebraic starting point for support propagation by translation. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- A functional kills all even polynomials if and only if it is odd under
reflection. -/
theorem even_tests_iff_odd_reflection (W : K[X] →ₗ[K] K) :
    (∀ q : K[X], W (q.comp (X^2)) = 0) ↔
      (∀ f : K[X], W (f.comp (-X)) = -W f) := by
  constructor
  · intro h f
    conv_lhs => rw [f.as_sum_range_C_mul_X_pow]
    conv_rhs => rw [f.as_sum_range_C_mul_X_pow]
    simp only [Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.pow_comp, Polynomial.X_comp, ← Polynomial.smul_eq_C_mul,
      map_sum, map_smul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rcases Nat.even_or_odd j with hj | hj
    · obtain ⟨a, ha⟩ := hj
      have hz := h (X^a)
      have heq : (X^a : K[X]).comp (X^2) = X^j := by
        simp only [Polynomial.pow_comp, Polynomial.X_comp, ← pow_mul]
        congr 1
        omega
      rw [heq] at hz
      have heven : Even j := ⟨a, ha⟩
      simp [heven.neg_pow, hz]
    · simp [hj.neg_pow]
  · intro h q
    have href := h (q.comp (X^2))
    have heq : (q.comp (X^2)).comp (-X) = q.comp (X^2) := by
      rw [Polynomial.comp_assoc]
      congr 1
      simp
    rw [heq] at href
    have hz : (2:K) * W (q.comp (X^2)) = 0 := by
      rw [two_mul, add_eq_zero_iff_eq_neg]
      exact href
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

def translatedFunctional (W : K[X] →ₗ[K] K) : K[X] →ₗ[K] K where
  toFun f := W (f.comp (X+1))
  map_add' f g := by simp
  map_smul' c f := by simp

/-- The test polynomials `q((z+1)^2)` are the fixed polynomials of the
reflection `z ↦ -2-z`. Killing them makes the functional odd under that
reflection. -/
theorem shifted_even_tests_iff_affine_reflection (W : K[X] →ₗ[K] K) :
    (∀ q : K[X], W (q.comp ((X+1)^2)) = 0) ↔
      (∀ f : K[X], W (f.comp (-X-2)) = -W f) := by
  have ht (q : K[X]) :
      translatedFunctional W (q.comp (X^2)) = W (q.comp ((X+1)^2)) := by
    change W ((q.comp (X^2)).comp (X+1)) = _
    simp [Polynomial.comp_assoc]
  constructor
  · intro h f
    have hT : ∀ q : K[X], translatedFunctional W (q.comp (X^2)) = 0 := by
      intro q
      rw [ht]
      exact h q
    have href := (even_tests_iff_odd_reflection (translatedFunctional W)).mp hT
      (f.comp (X-1))
    change W (((f.comp (X-1)).comp (-X)).comp (X+1)) =
      -W ((f.comp (X-1)).comp (X+1)) at href
    have hleft : ((f.comp (X-1)).comp (-X)).comp (X+1) = f.comp (-X-2) := by
      simp only [Polynomial.comp_assoc, Polynomial.sub_comp,
        Polynomial.X_comp, Polynomial.one_comp, Polynomial.neg_comp]
      congr 1
      ring
    have hright : (f.comp (X-1)).comp (X+1) = f := by
      simp [Polynomial.comp_assoc]
    rwa [hleft, hright] at href
  · intro h q
    have href := h (q.comp ((X+1)^2))
    have heq : (q.comp ((X+1)^2)).comp (-X-2) = q.comp ((X+1)^2) := by
      rw [Polynomial.comp_assoc]
      congr 1
      simp only [Polynomial.pow_comp, Polynomial.add_comp, Polynomial.X_comp,
        Polynomial.one_comp]
      ring
    rw [heq] at href
    have hz : (2:K) * W (q.comp ((X+1)^2)) = 0 := by
      rw [two_mul, add_eq_zero_iff_eq_neg]
      exact href
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-- The finite Pearson equation yields the second reflection identity used
to propagate support. This statement does not assume a jet decomposition. -/
theorem finitePearson_affine_reflection (A : K[X]) (U : K[X] →ₗ[K] K)
    (hU : IsFinitePearson A U) (f : K[X]) :
    U (A * f.comp (-X-2)) = -U (A*f) := by
  let W : K[X] →ₗ[K] K := {
    toFun := fun f => U (A*f)
    map_add' := by intros; simp [mul_add]
    map_smul' := by intros; simp }
  exact (shifted_even_tests_iff_affine_reflection W).mp hU.2.2 f

end OddZeta.FourValue

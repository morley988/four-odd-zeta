import Mathlib.Algebra.Polynomial.Expand
import FourValuePearsonBridge
import Mathlib.Tactic

/-! Local jet order under multiplication by a polynomial. These lemmas
formalize the order-drop rule used in finite Pearson classification. -/

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K]

def JetBound (U : K[X] →ₗ[K] K) (d : ℕ) : Prop :=
  ∀ k : ℕ, d < k → U (X ^ k) = 0

def ExactJetOrder (U : K[X] →ₗ[K] K) (d : ℕ) : Prop :=
  JetBound U d ∧ U (X ^ d) ≠ 0

def jetMultiply (a : K[X]) (U : K[X] →ₗ[K] K) : K[X] →ₗ[K] K where
  toFun f := U (a * f)
  map_add' f g := by simp [mul_add]
  map_smul' c f := by simp

@[simp] theorem jetMultiply_apply (a : K[X]) (U : K[X] →ₗ[K] K) (f : K[X]) :
    jetMultiply a U f = U (a * f) := rfl

/-- A bounded jet vanishes on every multiple of a sufficiently high power. -/
theorem jetBound_vanishes_multiple (U : K[X] →ₗ[K] K) (d : ℕ)
    (hU : JetBound U d) (b : K[X]) (k : ℕ) (hk : d < k) :
    U (b * X ^ k) = 0 := by
  conv_lhs => rw [b.as_sum_range_C_mul_X_pow]
  rw [Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [mul_assoc, ← pow_add, ← Polynomial.smul_eq_C_mul, map_smul]
  rw [hU (j + k) (by omega), smul_zero]

/-- At its highest derivative order only the multiplier's constant term
contributes. -/
theorem jetBound_top_multiply (U : K[X] →ₗ[K] K) (d : ℕ)
    (hU : JetBound U d) (b : K[X]) :
    U (b * X ^ d) = b.coeff 0 * U (X ^ d) := by
  have hz : U ((X * b.divX) * X ^ d) = 0 := by
    have heq : (X * b.divX) * X ^ d = b.divX * X ^ (d + 1) := by
      rw [pow_succ]
      ring
    simp only [heq]
    exact jetBound_vanishes_multiple U d hU b.divX (d+1) (by omega)
  conv_lhs => rw [← b.X_mul_divX_add]
  rw [add_mul, map_add, hz, zero_add, ← Polynomial.smul_eq_C_mul, map_smul]
  rfl

/-- A zero of multiplicity greater than the jet order kills the jet. -/
theorem jetMultiply_kills (U : K[X] →ₗ[K] K) (d t : ℕ)
    (hU : JetBound U d) (ht : d < t) (b : K[X]) :
    jetMultiply (X ^ t * b) U = 0 := by
  apply LinearMap.ext
  intro f
  change U (X ^ t * b * f) = 0
  rw [show X ^ t * b * f = (b * f) * X ^ t by ring]
  exact jetBound_vanishes_multiple U d hU (b * f) t ht

/-- Otherwise the highest jet order drops by exactly the multiplicity of
the multiplier's zero. This includes repeated roots. -/
theorem jetMultiply_exact_order (U : K[X] →ₗ[K] K) (d t : ℕ)
    (hU : ExactJetOrder U d) (ht : t ≤ d) (b : K[X]) (hb : b.coeff 0 ≠ 0) :
    ExactJetOrder (jetMultiply (X ^ t * b) U) (d - t) := by
  constructor
  · intro k hk
    change U (X ^ t * b * X ^ k) = 0
    rw [show X ^ t * b * X ^ k = b * X ^ (t + k) by rw [pow_add]; ring]
    exact jetBound_vanishes_multiple U d hU.1 b (t+k) (by omega)
  · change U (X ^ t * b * X ^ (d - t)) ≠ 0
    rw [show X ^ t * b * X ^ (d-t) = b * X ^ d by
      rw [mul_comm (X ^ t) b, mul_assoc, ← pow_add]
      rw [show t + (d-t) = d by omega]]
    rw [jetBound_top_multiply U d hU.1 b]
    exact mul_ne_zero hb hU.2

/-- Multiplication by a unit at the point preserves the highest jet order. -/
theorem jetMultiply_unit_preserves_order (U : K[X] →ₗ[K] K) (d : ℕ)
    (hU : ExactJetOrder U d) (b : K[X]) (hb : b.coeff 0 ≠ 0) :
    ExactJetOrder (jetMultiply b U) d := by
  simpa using jetMultiply_exact_order U d 0 hU (Nat.zero_le d) b hb

/-- Reflection-odd finite jets have odd highest order. -/
theorem odd_jet_has_odd_order [CharZero K] (U : K[X] →ₗ[K] K) (d : ℕ)
    (hU : ExactJetOrder U d)
    (hreflect : ∀ f : K[X], U (f.comp (-X)) = -U f) : Odd d := by
  rcases Nat.even_or_odd d with hd | hd
  · have href := hreflect (X ^ d)
    have heq : (X ^ d : K[X]).comp (-X) = X ^ d := by
      simp [Polynomial.pow_comp, hd.neg_pow]
    rw [heq] at href
    have hz : (2 : K) * U (X ^ d) = 0 := by
      rw [two_mul, add_eq_zero_iff_eq_neg]
      exact href
    exact False.elim (hU.2 ((mul_eq_zero.mp hz).resolve_left (by norm_num)))
  · exact hd

def admissibleCenterOrders : Finset ℕ := (Finset.range 15).filter Odd

theorem admissibleCenterOrders_eq :
    admissibleCenterOrders = {1,3,5,7,9,11,13} := by decide

theorem admissibleCenterOrders_card : admissibleCenterOrders.card = 7 := by decide

theorem odd_functional_even_moment [CharZero K] (U : K[X] →ₗ[K] K)
    (hreflect : ∀ f : K[X], U (f.comp (-X)) = -U f)
    (j : ℕ) (hj : Even j) : U (X ^ j) = 0 := by
  have href := hreflect (X ^ j)
  have heq : (X ^ j : K[X]).comp (-X) = X ^ j := by
    simp [Polynomial.pow_comp, hj.neg_pow]
  rw [heq] at href
  have hz : (2 : K) * U (X ^ j) = 0 := by
    rw [two_mul, add_eq_zero_iff_eq_neg]
    exact href
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

def centerJetBasis (i : Fin 7) : K[X] →ₗ[K] K :=
  Polynomial.lcoeff K (2 * i.val + 1)

theorem centerJetBasis_dual (i j : Fin 7) :
    centerJetBasis (K := K) i (X ^ (2 * j.val + 1)) = if i = j then 1 else 0 := by
  simp only [centerJetBasis, Polynomial.lcoeff_apply, Polynomial.coeff_X_pow]
  have heq : 2 * i.val + 1 = 2 * j.val + 1 ↔ i = j := by
    constructor
    · intro h
      apply Fin.ext
      omega
    · rintro rfl
      rfl
  simp only [heq]

theorem centerJetBasis_independent :
    LinearIndependent K (centerJetBasis (K := K)) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  intro j
  have h := congrArg (fun L : K[X] →ₗ[K] K => L (X ^ (2 * j.val + 1))) ha
  simpa [LinearMap.sum_apply, LinearMap.smul_apply, centerJetBasis_dual,
    smul_eq_mul] using h

/-- Every odd jet of order below fifteen is a unique combination of the
seven center coefficient jets. This verifies the local dimension statement;
global support propagation is still a separate classification step. -/
theorem odd_jet_center_expansion [CharZero K] (U : K[X] →ₗ[K] K)
    (hbound : JetBound U 14)
    (hreflect : ∀ f : K[X], U (f.comp (-X)) = -U f) :
    U = ∑ i : Fin 7, U (X ^ (2 * i.val + 1)) • centerJetBasis i := by
  apply sub_eq_zero.mp
  apply linearFunctional_zero_of_powers
  intro j
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    sub_eq_zero]
  by_cases hj : j < 15
  · rcases Nat.even_or_odd j with heven | ⟨k, hk⟩
    · rw [odd_functional_even_moment U hreflect j heven]
      symm
      apply Finset.sum_eq_zero
      intro i _
      have hne : j ≠ 2 * i.val + 1 := by
        intro heq
        rw [heq] at heven
        rcases heven with ⟨a, ha⟩
        omega
      simp [centerJetBasis, Polynomial.coeff_X_pow, Ne.symm hne]
    · let i : Fin 7 := ⟨k, by omega⟩
      have hji : j = 2 * i.val + 1 := by dsimp [i]; omega
      rw [hji]
      simp [centerJetBasis_dual, smul_eq_mul]
  · rw [hbound j (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hne : j ≠ 2 * i.val + 1 := by omega
    simp [centerJetBasis, Polynomial.coeff_X_pow, Ne.symm hne]

end OddZeta.FourValue

import FourValueOddLift
import FourValueCore
import Mathlib.Algebra.Polynomial.BigOperators

/-! The actual polynomial difference operator, its degree budget, and its
relationship to the odd lifted Pearson functional. -/

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K]

def pearsonOperator (A : K[X]) : K[X] →ₗ[K] K[X] where
  toFun q := (2 : K) • oddCompress (A * q.comp ((X + 1) ^ 2))
  map_add' f g := by simp [Polynomial.add_comp, mul_add, smul_add]
  map_smul' a f := by
    simp only [Polynomial.smul_comp, mul_smul_comm, map_smul, smul_smul,
      RingHom.id_apply]
    rw [mul_comm]

@[simp] theorem pearsonOperator_apply (A q : K[X]) :
    pearsonOperator A q = (2 : K) • oddCompress (A * q.comp ((X + 1) ^ 2)) := rfl

/-- Degree increase is at most nine when the Pearson polynomial has degree
at most twenty; the even top power disappears under odd extraction. -/
theorem pearsonOperator_degree (A q : K[X]) (hA : A.natDegree ≤ 20) :
    (pearsonOperator A q).natDegree ≤ q.natDegree + 9 := by
  apply (Polynomial.natDegree_smul_le _ _).trans
  apply oddCompress_degree_bound
  have h1 := Polynomial.natDegree_mul_le (p := A) (q := q.comp ((X + 1) ^ 2))
  have h2 := Polynomial.natDegree_comp_le (p := q) (q := (X + 1) ^ 2)
  have h3 : (((X : K[X]) + 1) ^ 2).natDegree = 2 := by
    simpa using Polynomial.natDegree_pow_X_add_C 2 (1 : K)
  rw [h3] at h2
  omega

theorem pearsonOperator_monomial_degree (A : K[X]) (hA : A.natDegree ≤ 20)
    (k : ℕ) : (pearsonOperator A (X ^ k)).natDegree ≤ k + 9 := by
  simpa using pearsonOperator_degree A (X ^ k) hA

/-- This identity connects the difference relation to the lifted functional. -/
theorem pearsonOperator_observation (A q : K[X]) (L : K[X] →ₗ[K] K) :
    L (pearsonOperator A q) = 2 * oddLift L (A * q.comp ((X + 1) ^ 2)) := by
  simp [pearsonOperator_apply, smul_eq_mul]

theorem pearsonOperator_test_zero [CharZero K]
    (A : K[X]) (L : K[X] →ₗ[K] K) (j : ℕ)
    (h : L (pearsonOperator A (X ^ j)) = 0) :
    oddLift L (A * ((X + 1) ^ 2) ^ j) = 0 := by
  rw [pearsonOperator_observation] at h
  have h2 : (2 : K) ≠ 0 := by norm_num
  simpa using (mul_eq_zero.mp h).resolve_left h2

/-- A monic product with its root list kept explicit. -/
def linearRootProduct (roots : List K) : K[X] :=
  (roots.map fun a => X - C a).prod

theorem linearRootProduct_monic (roots : List K) :
    (linearRootProduct roots).Monic := by
  induction roots with
  | nil => simp [linearRootProduct]
  | cons a roots ih =>
      change ((X - C a) * linearRootProduct roots).Monic
      exact (Polynomial.monic_X_sub_C a).mul ih

theorem linearRootProduct_degree (roots : List K) :
    (linearRootProduct roots).natDegree = roots.length := by
  induction roots with
  | nil => simp [linearRootProduct]
  | cons a roots ih =>
      change ((X - C a) * linearRootProduct roots).natDegree = roots.length + 1
      rw [(Polynomial.monic_X_sub_C a).natDegree_mul (linearRootProduct_monic roots),
        Polynomial.natDegree_X_sub_C, ih]
      omega

theorem linearRootProduct_nextCoeff (roots : List K) :
    (linearRootProduct roots).nextCoeff = -roots.sum := by
  induction roots with
  | nil => simp [linearRootProduct, Polynomial.nextCoeff]
  | cons a roots ih =>
      change ((X - C a) * linearRootProduct roots).nextCoeff = -(a + roots.sum)
      rw [(Polynomial.monic_X_sub_C a).nextCoeff_mul (linearRootProduct_monic roots),
        Polynomial.nextCoeff_X_sub_C, ih]
      ring

def physicalEndpointRoots (n : K) : List K :=
  [134*n,134*n,134*n,134*n,134*n,126*n,120*n,116*n,114*n,
    108*n,104*n,98*n,94*n,88*n,84*n]

/-- The manuscript's exact degree-twenty Pearson polynomial. -/
def pearsonPolynomial (n : K) : K[X] :=
  (X + C (200*n+2)) ^ 5 * linearRootProduct (physicalEndpointRoots n)

theorem pearsonPolynomial_monic (n : K) : (pearsonPolynomial n).Monic :=
  ((Polynomial.monic_X_add_C _).pow 5).mul (linearRootProduct_monic _)

theorem pearsonPolynomial_degree (n : K) : (pearsonPolynomial n).natDegree = 20 := by
  rw [pearsonPolynomial,
    ((Polynomial.monic_X_add_C _).pow 5).natDegree_mul (linearRootProduct_monic _),
    Polynomial.natDegree_pow_X_add_C, linearRootProduct_degree]
  simp [physicalEndpointRoots]

theorem pearsonPolynomial_nextCoeff (n : K) :
    (pearsonPolynomial n).nextCoeff = 10 - 722 * n := by
  rw [pearsonPolynomial,
    ((Polynomial.monic_X_add_C _).pow 5).nextCoeff_mul (linearRootProduct_monic _),
    (Polynomial.monic_X_add_C _).nextCoeff_pow, Polynomial.nextCoeff_X_add_C,
    linearRootProduct_nextCoeff]
  simp [physicalEndpointRoots]
  ring

theorem actualPearson_degree (n : K) (q : K[X]) :
    (pearsonOperator (pearsonPolynomial n) q).natDegree ≤ q.natDegree + 9 :=
  pearsonOperator_degree _ _ (le_of_eq (pearsonPolynomial_degree n))

/-- The coefficient at the predicted top degree, with the exact manuscript
normalization. It need not be nonzero in exceptional degrees. -/
theorem actualPearson_monomial_top_coefficient (n : K) (k : ℕ) :
    (pearsonOperator (pearsonPolynomial n) (X ^ k)).coeff (k + 9) =
      4 * ((k : K) - 361 * n + 5) := by
  let F : K[X] := pearsonPolynomial n * (X + C (1 : K)) ^ (2 * k)
  have hmon : F.Monic := (pearsonPolynomial_monic n).mul
    ((Polynomial.monic_X_add_C _).pow _)
  have hdeg : F.natDegree = 20 + 2 * k := by
    dsimp [F]
    rw [(pearsonPolynomial_monic n).natDegree_mul
      ((Polynomial.monic_X_add_C _).pow _), pearsonPolynomial_degree,
      Polynomial.natDegree_pow_X_add_C]
  have hn : F.nextCoeff = 10 - 722 * n + 2 * (k : K) := by
    dsimp [F]
    rw [(pearsonPolynomial_monic n).nextCoeff_mul
      ((Polynomial.monic_X_add_C _).pow _), pearsonPolynomial_nextCoeff,
      (Polynomial.monic_X_add_C _).nextCoeff_pow, Polynomial.nextCoeff_X_add_C]
    simp
  have hc : F.coeff (2 * (k + 9) + 1) = F.nextCoeff := by
    rw [Polynomial.nextCoeff_of_natDegree_pos (by omega), hdeg]
    congr 1
    omega
  rw [pearsonOperator_apply, Polynomial.coeff_smul, oddCompress_coeff]
  have heq : (pearsonPolynomial n * (X ^ k).comp ((X + 1) ^ 2) : K[X]) = F := by
    simp [F, Polynomial.pow_comp, ← pow_mul]
  rw [heq, hc, hn]
  simp only [smul_eq_mul]
  ring

theorem actualPearson_monomial_degree [CharZero K] (n k : ℕ)
    (hk : k + 6 ≤ 361 * n) :
    (pearsonOperator (pearsonPolynomial (n : K)) (X ^ k)).natDegree = k + 9 := by
  have hz : ((k : ℤ) - 361 * (n : ℤ) + 5) ≠ 0 := by omega
  have hzK : (k : K) - 361 * (n : K) + 5 ≠ 0 := by
    exact_mod_cast hz
  have hc : (pearsonOperator (pearsonPolynomial (n : K)) (X ^ k)).coeff (k + 9) ≠ 0 := by
    rw [actualPearson_monomial_top_coefficient]
    exact mul_ne_zero (by norm_num) hzK
  apply le_antisymm
  · simpa using actualPearson_degree (n : K) (X ^ k)
  · exact Polynomial.le_natDegree_of_ne_zero hc

end OddZeta.FourValue

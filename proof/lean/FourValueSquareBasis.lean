import FourValueHankelExtension
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-! The manuscript's squared-variable polynomial basis, its invertible
coefficient matrix, and rank invariance for actual moment Gram matrices. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def squareRootProduct (i : ℕ) : K[X] :=
  linearRootProduct ((List.range i).map (fun h : ℕ => (h:K)^2))

theorem squareRootProduct_monic (i : ℕ) : (squareRootProduct (K:=K) i).Monic :=
  linearRootProduct_monic _

theorem squareRootProduct_degree (i : ℕ) : (squareRootProduct (K:=K) i).natDegree=i := by
  simp [squareRootProduct,linearRootProduct_degree]

def squareBasisPolynomial (i : ℕ) : K[X] :=
  if i=0 then 1 else C ((2:K)/(Nat.factorial (2*i):K))*squareRootProduct i

theorem squareBasisPolynomial_degree (i : ℕ) :
    (squareBasisPolynomial (K:=K) i).natDegree=i := by
  by_cases hi : i=0
  · simp [squareBasisPolynomial,hi]
  · have hc : (2:K)/(Nat.factorial (2*i):K)≠0 := div_ne_zero
      (by norm_num) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    rw [squareBasisPolynomial,if_neg hi,
      Polynomial.natDegree_C_mul_of_isUnit hc.isUnit,squareRootProduct_degree]

theorem squareBasisPolynomial_leadingCoeff (i : ℕ) :
    (squareBasisPolynomial (K:=K) i).leadingCoeff =
      if i=0 then 1 else (2:K)/(Nat.factorial (2*i):K) := by
  by_cases hi : i=0
  · simp [squareBasisPolynomial,hi]
  · rw [squareBasisPolynomial,if_neg hi,if_neg hi,
      (squareRootProduct_monic i).leadingCoeff_C_mul]

theorem squareBasisPolynomial_leadingCoeff_ne_zero (i : ℕ) :
    (squareBasisPolynomial (K:=K) i).leadingCoeff≠0 := by
  rw [squareBasisPolynomial_leadingCoeff]
  split_ifs
  · exact one_ne_zero
  · exact div_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

def squareBasisMatrix (m : ℕ) : Matrix (Fin (m+1)) (Fin (m+1)) K :=
  fun i j => (squareBasisPolynomial j.val).coeff i.val

theorem squareBasisMatrix_det_ne_zero (m : ℕ) : (squareBasisMatrix (K:=K) m).det≠0 := by
  have htri : (squareBasisMatrix (K:=K) m).IsUpperTriangular := by
    intro i j hij
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [squareBasisPolynomial_degree]
    exact hij
  rw [Matrix.det_of_isUpperTriangular htri]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  change (squareBasisPolynomial (K:=K) i.val).coeff i.val≠0
  have hc := Polynomial.coeff_natDegree (p:=squareBasisPolynomial (K:=K) i.val)
  rw [squareBasisPolynomial_degree] at hc
  rw [hc]
  exact squareBasisPolynomial_leadingCoeff_ne_zero i.val

/-- Finite coefficient reconstruction, at the exact matrix size. -/
theorem polynomial_finite_expansion (m : ℕ) (q : K[X]) (hq : q.natDegree≤m) :
    q=∑ i : Fin (m+1), C (q.coeff i.val)*X^i.val := by
  have h := polynomialFromVector_of_coeffs m q hq
  change (∑ i : Fin (m+1), Polynomial.monomial i.val (q.coeff i.val))=q at h
  simpa only [Polynomial.C_mul_X_pow_eq_monomial] using h.symm

def polynomialCoefficientMatrix (m : ℕ) (q : Fin (m+1) → K[X]) :
    Matrix (Fin (m+1)) (Fin (m+1)) K := fun i j => (q j).coeff i.val

/-- Polynomial changes of basis act on a moment Gram matrix by congruence. -/
theorem momentGram_change_of_basis (L : K[X] →ₗ[K] K) (m : ℕ)
    (q : Fin (m+1) → K[X]) (hq : ∀ i, (q i).natDegree≤m) :
    (fun i j => L (q i*q j) : Matrix (Fin (m+1)) (Fin (m+1)) K) =
      (polynomialCoefficientMatrix m q).transpose * momentHankel L m *
        polynomialCoefficientMatrix m q := by
  ext i j
  conv_lhs => rw [polynomial_finite_expansion m (q i) (hq i),
    polynomial_finite_expansion m (q j) (hq j)]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,momentHankel,polynomialCoefficientMatrix,
    Finset.sum_mul,Finset.mul_sum,map_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [show (C ((q i).coeff a.val)*X^a.val)*(C ((q j).coeff b.val)*X^b.val) =
      (((q i).coeff a.val)*((q j).coeff b.val)) • X^(a.val+b.val) by
        rw [Polynomial.smul_eq_C_mul,map_mul,pow_add]; ring,
    map_smul]
  simp only [smul_eq_mul]
  ring

def squareBasisGram (L : K[X] →ₗ[K] K) (m : ℕ) :
    Matrix (Fin (m+1)) (Fin (m+1)) K :=
  fun i j => L (squareBasisPolynomial i.val * squareBasisPolynomial j.val)

theorem squareBasisGram_rank (L : K[X] →ₗ[K] K) (m : ℕ) :
    (squareBasisGram L m).rank=(momentHankel L m).rank := by
  have hq : ∀ i : Fin (m+1), (squareBasisPolynomial (K:=K) i.val).natDegree≤m := by
    intro i
    rw [squareBasisPolynomial_degree]
    omega
  have heq := momentGram_change_of_basis L m (fun i => squareBasisPolynomial i.val) hq
  change squareBasisGram L m = (squareBasisMatrix m).transpose * momentHankel L m *
    squareBasisMatrix m at heq
  rw [heq,Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (squareBasisMatrix_det_ne_zero m),
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _]
  simpa using squareBasisMatrix_det_ne_zero (K:=K) m

/-- Selection in the manuscript's actual polynomial basis. The remaining
initial-vector exclusion is stated openly as an input. -/
theorem squareBasis_nonzero_minor_of_finite_exclusion (L : K[X] →ₗ[K] K) (A : K[X]) (m : ℕ)
    (hA : A.natDegree≤20)
    (hrel : ∀ j : ℕ, j+9≤2*m → L (pearsonOperator A (X^j))=0)
    (hexclusion : ∀ U : K[X] →ₗ[K] K, IsFinitePearson A U →
      liftedInitialMoments U≠initialMoments L) :
    ∃ rows cols : Fin (m+1-4) ↪ Fin (m+1),
      ((squareBasisGram L m).submatrix rows cols).det≠0 := by
  apply rank_selects_nonzero_minor
  rw [squareBasisGram_rank]
  exact hankel_rank_bound_of_finite_exclusion L A m hA hrel hexclusion

end OddZeta.FourValue

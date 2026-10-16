import FourValueSquareBasis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! The exact five-by-five polynomial antidifference system at the
independence seed. Tail summation and Taylor-jet identification are separate
analytic steps and are not assumed in these algebraic statements. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def seedAntidifference (b : K) : K[X] →ₗ[K] K[X] where
  toFun p := (X+C b)*p-(X-C b)*p.comp (X+1)
  map_add' p q := by simp [Polynomial.add_comp]; ring
  map_smul' c p := by simp [Polynomial.smul_comp, smul_sub]

def seedPolynomial (c : Fin 5 → K) : K[X] :=
  ∑ h : Fin 5, c h • (X*(X-1))^h.val

def seedEvenPolynomial (c : Fin 5 → K) : K[X] :=
  ∑ h : Fin 5, c h • X^(2*h.val)

def seedCoefficientMatrix (b : K) : Matrix (Fin 5) (Fin 5) K :=
  !![2*b, 0, 0, 0, 0;
     0, 2*b-2, 2*b, 0, 0;
     0, 0, 2*b-4, 6*b-2, 2*b;
     0, 0, 0, 2*b-6, 12*b-8;
     0, 0, 0, 0, 2*b-8]

/-- Each column is the exact even polynomial image of its seed basis element. -/
theorem seedAntidifference_basis (b : K) (h : Fin 5) :
    seedAntidifference b ((X*(X-1))^h.val) =
      seedEvenPolynomial (fun i => seedCoefficientMatrix b i h) := by
  fin_cases h <;>
    norm_num [seedAntidifference, seedEvenPolynomial, seedCoefficientMatrix,
      Fin.sum_univ_succ, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.sub_comp, Polynomial.X_comp, Polynomial.one_comp,
      Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_ofNat] <;> ring

theorem seedCoefficientMatrix_upper (b : K) :
    (seedCoefficientMatrix b).IsUpperTriangular := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals simp_all [seedCoefficientMatrix]

theorem seedCoefficientMatrix_det (b : K) :
    (seedCoefficientMatrix b).det = 32*b*(b-1)*(b-2)*(b-3)*(b-4) := by
  rw [Matrix.det_of_isUpperTriangular (seedCoefficientMatrix_upper b)]
  norm_num [seedCoefficientMatrix, Fin.prod_univ_succ]
  ring

theorem seedCoefficientMatrix_det_ne_zero (b : K)
    (hb : ∀ h : Fin 5, b≠(h.val:K)) : (seedCoefficientMatrix b).det≠0 := by
  rw [seedCoefficientMatrix_det]
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · exact mul_ne_zero (by norm_num) (by simpa using hb 0)
        · exact sub_ne_zero.mpr (by simpa using hb 1)
      · exact sub_ne_zero.mpr (by simpa using hb 2)
    · exact sub_ne_zero.mpr (by simpa using hb 3)
  · exact sub_ne_zero.mpr (by simpa using hb 4)

theorem seedAntidifference_matrix (b : K) (c : Fin 5 → K) :
    seedAntidifference b (seedPolynomial c) =
      seedEvenPolynomial ((seedCoefficientMatrix b).mulVec c) := by
  simp only [seedPolynomial, map_sum, map_smul, seedAntidifference_basis,
    seedEvenPolynomial, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro h _
  rw [mul_comm]

theorem seedEvenPolynomial_coeff (c : Fin 5 → K) (i : Fin 5) :
    (seedEvenPolynomial c).coeff (2*i.val) = c i := by
  simp only [seedEvenPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
    Polynomial.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  have heq (j : Fin 5) : 2*i.val=2*j.val ↔ j=i := by
    constructor
    · intro h
      apply Fin.ext
      omega
    · rintro rfl
      rfl
  simp_rw [heq]
  simp

theorem seedEvenPolynomial_injective :
    Function.Injective (seedEvenPolynomial (K:=K)) := by
  intro c d h
  funext i
  have hc := congrArg (fun p : K[X] => p.coeff (2*i.val)) h
  simpa only [seedEvenPolynomial_coeff] using hc

/-- The exact five-dimensional seed antidifference system has a unique
solution for every even right-hand side of degree at most eight. -/
theorem seedAntidifference_exists_unique (b : K)
    (hb : ∀ h : Fin 5, b≠(h.val:K)) (v : Fin 5 → K) :
    ∃! c : Fin 5 → K,
      seedAntidifference b (seedPolynomial c)=seedEvenPolynomial v := by
  have hunit : IsUnit (seedCoefficientMatrix b) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (seedCoefficientMatrix_det_ne_zero b hb).isUnit
  obtain ⟨c,hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hunit v
  refine ⟨c,?_,?_⟩
  · change seedAntidifference b (seedPolynomial c)=seedEvenPolynomial v
    rw [seedAntidifference_matrix,hc]
  · intro d hd
    rw [seedAntidifference_matrix] at hd
    have hd' := seedEvenPolynomial_injective hd
    exact (Matrix.mulVec_injective_iff_isUnit.mpr hunit) (hd'.trans hc.symm)

theorem seedAntidifference_monomial (b : K)
    (hb : ∀ h : Fin 5, b≠(h.val:K)) (l : Fin 5) :
    ∃! c : Fin 5 → K,
      seedAntidifference b (seedPolynomial c)=(2:K) • X^(2*l.val) := by
  have h := seedAntidifference_exists_unique b hb (fun i => if i=l then 2 else 0)
  simpa [seedEvenPolynomial] using h

theorem seed_natural_parameter (b : ℕ) (hb : 5≤b) :
    ∀ h : Fin 5, (b:K)≠(h.val:K) := by
  intro h heq
  have hc : b=h.val := Nat.cast_injective heq
  omega

/-- The local substitution x(x-1), centered at x=b+1, is
u ↦ (2b+1)u+u² after subtracting its constant value. -/
theorem seed_centered_substitution (b : K) :
    ((X+C (b+1))*(X+C b)-C (b*(b+1)) : K[X]) = C (2*b+1)*X+X^2 := by
  simp only [map_add,map_mul,map_ofNat,map_one]
  ring

def seedJetMatrix (c : K) : Matrix (Fin 5) (Fin 5) K :=
  !![1, 0, 0, 0, 0;
     0, c, 0, 0, 0;
     0, 1, c^2, 0, 0;
     0, 0, 2*c, c^3, 0;
     0, 0, 1, 3*c^2, c^4]

set_option maxHeartbeats 2000000 in
/-- This is the actual matrix of substitution on coefficients through order four. -/
theorem seedJetMatrix_coeff (c : K) (i h : Fin 5) :
    ((C c*X+X^2)^h.val : K[X]).coeff i.val=seedJetMatrix c i h := by
  fin_cases h <;> fin_cases i
  all_goals norm_num [seedJetMatrix, pow_succ, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Polynomial.coeff_one,Polynomial.coeff_X,Polynomial.coeff_C]
  all_goals ring

theorem seedJetMatrix_det (c : K) : (seedJetMatrix c).det=c^10 := by
  have htri : (seedJetMatrix c).transpose.IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals simp_all [seedJetMatrix,Matrix.transpose_apply]
  rw [← Matrix.det_transpose, Matrix.det_of_isUpperTriangular htri]
  norm_num [seedJetMatrix,Matrix.transpose_apply,Fin.prod_univ_succ]
  ring

theorem seedJetMatrix_det_ne_zero (c : K) (hc : c≠0) :
    (seedJetMatrix c).det≠0 := by
  rw [seedJetMatrix_det]
  exact pow_ne_zero _ hc

theorem seed_actual_jet_matrix_nonzero (b : ℕ) :
    (seedJetMatrix (2*(b:K)+1)).det≠0 := by
  apply seedJetMatrix_det_ne_zero
  have h : ((2*b+1:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (by omega)
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using h

end OddZeta.FourValue

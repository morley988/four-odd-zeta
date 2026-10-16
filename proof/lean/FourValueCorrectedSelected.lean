import FourValueCorrectedLocal

/-! Transfer local bounds to the actual E_i(x²) rows and columns, with factorial costs.
The physical-coordinate checkpoint remains unchanged; this namespace supplies
the arithmetic statements for the analytic-coordinate matrix. -/

noncomputable section
namespace OddZeta.FourValue.Corrected
open Polynomial
open scoped RatFunc
attribute [-instance] DivisionRing.toRatAlgebra
variable {p : ℕ} [Fact p.Prime]
def rationalAnalyticTestLinear (n : ℕ) : ℚ[X] →ₗ[ℚ] RatFunc ℚ where
  toFun := rationalAnalyticTest n
  map_add' P Q := by simp [rationalAnalyticTest,add_comp,map_add,mul_add]
  map_smul' q P := by
    simp [rationalAnalyticTest,smul_comp,map_smul,Algebra.smul_def,mul_left_comm,mul_assoc]

def residuePolynomialFunctional (n b : ℕ) (S : Finset ℤ) (lambda : Fin 4 → ℚ) : ℚ[X] →ₗ[ℚ] ℚ :=
  (∑ a ∈ S, localFourValueLinear b a lambda).comp (rationalAnalyticTestLinear n)

theorem residuePolynomialFunctional_apply (n b : ℕ) (S : Finset ℤ) (lambda : Fin 4 → ℚ) (P : ℚ[X]) :
    residuePolynomialFunctional n b S lambda P =
      ∑ a ∈ S,localFourValueObservation b a lambda (rationalAnalyticTest n P) := by
  simp [residuePolynomialFunctional,LinearMap.sum_apply,localFourValueLinear_apply,
    rationalAnalyticTestLinear]
  rfl

def selectedResidueMatrix (n b : ℕ) (S : Finset ℤ) (lambda : Fin 4 → ℚ) {k : ℕ}
    (rows cols : Fin k → Fin (targetHankelDegree n+1)) : Matrix (Fin k) (Fin k) ℚ :=
  polynomialGram (residuePolynomialFunctional n b S lambda)
    (fun i => squareBasisPolynomial (rows i).val) (fun j => squareBasisPolynomial (cols j).val)

theorem selectedResidueMatrix_transfer (n b : ℕ) (S : Finset ℤ) (r : ℤ) (lambda : Fin 4 → ℚ)
    {k : ℕ} (rows cols : Fin k → Fin (targetHankelDegree n+1)) (w : ℤ)
    (hM : ∀ u v : Fin k → Fin (targetHankelDegree n+1),
      PadicLower p w ((residueClassMatrix n b S r lambda Fin.val Fin.val).submatrix u v).det) :
    PadicLower p (w-selectedFactorialCost p n rows cols)
      (selectedResidueMatrix n b S lambda rows cols).det := by
  unfold selectedResidueMatrix
  rw [polynomialGram_translated _ _ _ ((r:ℚ)^2)
    (fun i => by rw [squareBasisPolynomial_degree]; exact (rows i).isLt)
    (fun j => by rw [squareBasisPolynomial_degree]; exact (cols j).isLt)]
  have he : (fun (l h : Fin (targetHankelDegree n+1)) =>
      residuePolynomialFunctional n b S lambda ((X-C ((r:ℚ)^2))^(l.val+h.val))) =
      residueClassMatrix n b S r lambda Fin.val Fin.val := by
    ext i j
    exact residuePolynomialFunctional_apply _ _ _ _ _
  rw [he]
  have hh := padicLower_det_weighted_change _ _ _ w
    (fun i => -(padicValNat p (2*(rows i).val).factorial:ℤ))
    (fun j => -(padicValNat p (2*(cols j).val).factorial:ℤ)) hM
    (fun i j => by simpa using squareBasis_taylor_coefficient_padicLower (rows i).val j.val (r^2))
    (fun i j => by simpa using squareBasis_taylor_coefficient_padicLower (cols j).val i.val (r^2))
  convert hh using 1
  · simp [selectedFactorialCost,Finset.sum_neg_distrib]
    ring
  · simp only [Int.cast_mul,Int.cast_ofNat,Int.cast_pow,Matrix.of_apply]
    rfl

theorem selectedResidueMatrix_bad_bound (n b : ℕ) (S : Finset ℤ) (r : ℤ) (lambda : Fin 4 → ℚ)
    {k : ℕ} (rows cols : Fin k → Fin (targetHankelDegree n+1))
    (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda)
    (hS : ∀ a∈S,a∈poleWindow (100*n) ∧ ((p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) ∧ (b-a).toNat<p^2) :
    PadicLower p ((k:ℤ)^2+(targetLocalWeight p n r-5)*k-selectedFactorialCost p n rows cols)
      (selectedResidueMatrix n b S lambda rows cols).det := by
  apply selectedResidueMatrix_transfer n b S r lambda rows cols
  intro u v
  by_cases hu : Function.Injective u
  · by_cases hv : Function.Injective v
    · exact pairedResidueClassMatrix_det_padicLower n b S r lambda
        (fun i => (u i).val) (fun j => (v j).val)
        (Fin.val_injective.comp hu) (Fin.val_injective.comp hv) hs hp hS
    · rw [matrix_submatrix_det_zero_of_not_injective _ _ _ (Or.inr hv)]
      exact PadicLower.zero _
  · rw [matrix_submatrix_det_zero_of_not_injective _ _ _ (Or.inl hu)]
    exact PadicLower.zero _

theorem selectedResidueMatrix_good_bound (n b : ℕ) (S : Finset ℤ) (r : ℤ) (lambda : Fin 4 → ℚ)
    {k : ℕ} (rows cols : Fin k → Fin (targetHankelDegree n+1))
    (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda)
    (hS : ∀ a∈S,a∈poleWindow (100*n) ∧ ((p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) ∧ (b-a).toNat<p) :
    PadicLower p ((k:ℤ)^2+targetLocalWeight p n r*k-selectedFactorialCost p n rows cols)
      (selectedResidueMatrix n b S lambda rows cols).det := by
  apply selectedResidueMatrix_transfer n b S r lambda rows cols
  intro u v
  by_cases hu : Function.Injective u
  · by_cases hv : Function.Injective v
    · exact pairedResidueClassMatrix_det_padicLower_good n b S r lambda
        (fun i => (u i).val) (fun j => (v j).val)
        (Fin.val_injective.comp hu) (Fin.val_injective.comp hv) hs hp hS
    · rw [matrix_submatrix_det_zero_of_not_injective _ _ _ (Or.inr hv)]
      exact PadicLower.zero _
  · rw [matrix_submatrix_det_zero_of_not_injective _ _ _ (Or.inl hu)]
    exact PadicLower.zero _

theorem rationalFourValueMatrix_selected_boundary (n : ℕ) (lambda : Fin 4 → ℚ) {k : ℕ}
    (rows cols : Fin k → Fin (targetHankelDegree n+1)) :
    (rationalFourValueMatrix n lambda).submatrix rows cols =
      selectedResidueMatrix n (67*n) (poleWindow (67*n)) lambda rows cols := by
  ext i j
  change rationalFourValueFunctional n lambda
    (squareBasisPolynomial (rows i).val*squareBasisPolynomial (cols j).val) = _
  rw [rationalFourValueFunctional_local_sum_67]
  · exact (residuePolynomialFunctional_apply _ _ _ _ _).symm
  · have h := Polynomial.natDegree_mul_le (p:=squareBasisPolynomial (K:=ℚ) (rows i).val)
      (q:=squareBasisPolynomial (K:=ℚ) (cols j).val)
    rw [squareBasisPolynomial_degree,squareBasisPolynomial_degree] at h
    have hr := (rows i).isLt
    have hc := (cols j).isLt
    unfold targetHankelDegree at hr hc
    omega


end OddZeta.FourValue.Corrected

attribute [instance] DivisionRing.toRatAlgebra

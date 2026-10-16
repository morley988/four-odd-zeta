import FourValueTaylorDenominators

noncomputable section
namespace OddZeta.FourValue
open Polynomial
open scoped RatFunc
attribute [-instance] DivisionRing.toRatAlgebra
variable {p : ℕ} [Fact p.Prime]

def rationalPhysicalTestLinear (n : ℕ) : ℚ[X] →ₗ[ℚ] RatFunc ℚ where
  toFun := rationalPhysicalTest n
  map_add' P Q := by simp [rationalPhysicalTest,add_comp,map_add,mul_add]
  map_smul' q P := by
    simp [rationalPhysicalTest,smul_comp,map_smul,Algebra.smul_def,mul_left_comm,mul_assoc]

def localFourValueLinear (b : ℕ) (a : ℤ) (lambda : Fin 4 → ℚ) : RatFunc ℚ →ₗ[ℚ] ℚ :=
  -(∑ k ∈ Finset.range 10,
    ((Nat.choose (k+4) 4:ℚ)*finiteHarmonic (K:=ℚ) (b-a).toNat (k+5)) •
      rationalCoefficientAt (a:ℚ) (-((k+1:ℕ):ℤ))) +
  lambda 0 • rationalCoefficientAt (a:ℚ) (-3) +
  lambda 1 • rationalCoefficientAt (a:ℚ) (-5) +
  lambda 2 • rationalCoefficientAt (a:ℚ) (-7) +
  lambda 3 • rationalCoefficientAt (a:ℚ) (-9)

theorem localFourValueLinear_apply (b : ℕ) (a : ℤ) (lambda : Fin 4 → ℚ) (f : RatFunc ℚ) :
    localFourValueLinear b a lambda f = localFourValueObservation b a lambda f := by
  simp [localFourValueLinear,localFourValueObservation,localFourthObservation,
    LinearMap.sum_apply,smul_eq_mul,mul_assoc]

def residuePolynomialFunctional (n b : ℕ) (S : Finset ℤ) (lambda : Fin 4 → ℚ) : ℚ[X] →ₗ[ℚ] ℚ :=
  (∑ a ∈ S, localFourValueLinear b a lambda).comp (rationalPhysicalTestLinear n)

theorem residuePolynomialFunctional_apply (n b : ℕ) (S : Finset ℤ) (lambda : Fin 4 → ℚ) (P : ℚ[X]) :
    residuePolynomialFunctional n b S lambda P =
      ∑ a ∈ S,localFourValueObservation b a lambda (rationalPhysicalTest n P) := by
  simp [residuePolynomialFunctional,LinearMap.sum_apply,localFourValueLinear_apply,
    rationalPhysicalTestLinear]
  rfl

def polynomialGram {k : ℕ} (L : ℚ[X] →ₗ[ℚ] ℚ) (P Q : Fin k → ℚ[X]) : Matrix (Fin k) (Fin k) ℚ :=
  fun i j => L (P i*Q j)

theorem polynomialGram_translated {k d : ℕ} (L : ℚ[X] →ₗ[ℚ] ℚ) (P Q : Fin k → ℚ[X]) (c : ℚ)
    (hP : ∀ i,(P i).natDegree<d) (hQ : ∀ j,(Q j).natDegree<d) :
    polynomialGram L P Q =
      (Matrix.of (fun i (l : Fin d) => ((P i).taylor c).coeff l.val) : Matrix (Fin k) (Fin d) ℚ) *
      (Matrix.of (fun (l h : Fin d) => L ((X-C c)^(l.val+h.val))) : Matrix (Fin d) (Fin d) ℚ) *
      (Matrix.of (fun (h : Fin d) j => ((Q j).taylor c).coeff h.val) : Matrix (Fin d) (Fin k) ℚ) := by
  ext i j
  change L (P i*Q j) = _
  rw [polynomial_translated_expansion (P i) c d (hP i),
    polynomial_translated_expansion (Q j) c d (hQ j)]
  simp only [Finset.sum_mul,Finset.mul_sum,map_sum,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro l hl
  rw [show C (((P i).taylor c).coeff l.val)*(X-C c)^l.val *
      (C (((Q j).taylor c).coeff h.val)*(X-C c)^h.val) =
      ((((P i).taylor c).coeff l.val)*(((Q j).taylor c).coeff h.val)) •
        (X-C c)^(l.val+h.val) by simp [pow_add,smul_eq_C_mul]; ring]
  simp [mul_comm,mul_left_comm,mul_assoc]

def selectedResidueMatrix (n b : ℕ) (S : Finset ℤ) (lambda : Fin 4 → ℚ) {k : ℕ}
    (rows cols : Fin k → Fin (targetHankelDegree n+1)) : Matrix (Fin k) (Fin k) ℚ :=
  polynomialGram (residuePolynomialFunctional n b S lambda)
    (fun i => squareBasisPolynomial (rows i).val) (fun j => squareBasisPolynomial (cols j).val)

def selectedFactorialCost (p n : ℕ) {k : ℕ} (rows cols : Fin k → Fin (targetHankelDegree n+1)) : ℤ :=
  (∑ i, (padicValNat p (2*(rows i).val).factorial:ℤ)) +
  (∑ j, (padicValNat p (2*(cols j).val).factorial:ℤ))

theorem selectedResidueMatrix_transfer (n b : ℕ) (S : Finset ℤ) (r : ℤ) (lambda : Fin 4 → ℚ)
    {k : ℕ} (rows cols : Fin k → Fin (targetHankelDegree n+1)) (w : ℤ)
    (hM : ∀ u v : Fin k → Fin (targetHankelDegree n+1),
      PadicLower p w ((residueClassMatrix n b S r lambda Fin.val Fin.val).submatrix u v).det) :
    PadicLower p (w-selectedFactorialCost p n rows cols)
      (selectedResidueMatrix n b S lambda rows cols).det := by
  unfold selectedResidueMatrix
  rw [polynomialGram_translated _ _ _ (4*(r:ℚ)^2)
    (fun i => by rw [squareBasisPolynomial_degree]; exact (rows i).isLt)
    (fun j => by rw [squareBasisPolynomial_degree]; exact (cols j).isLt)]
  have he : (fun (l h : Fin (targetHankelDegree n+1)) =>
      residuePolynomialFunctional n b S lambda ((X-C (4*(r:ℚ)^2))^(l.val+h.val))) =
      residueClassMatrix n b S r lambda Fin.val Fin.val := by
    ext i j
    exact residuePolynomialFunctional_apply _ _ _ _ _
  rw [he]
  have hh := padicLower_det_weighted_change _ _ _ w
    (fun i => -(padicValNat p (2*(rows i).val).factorial:ℤ))
    (fun j => -(padicValNat p (2*(cols j).val).factorial:ℤ)) hM
    (fun i j => by simpa using squareBasis_taylor_coefficient_padicLower (rows i).val j.val (4*r^2))
    (fun i j => by simpa using squareBasis_taylor_coefficient_padicLower (cols j).val i.val (4*r^2))
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

theorem selectedFactorialCost_large (n : ℕ) {k : ℕ}
    (rows cols : Fin k → Fin (targetHankelDegree n+1)) (hs : 800*n<p^2) :
    selectedFactorialCost p n rows cols =
      (∑ i,((2*(rows i).val/p:ℕ):ℤ))+(∑ j,((2*(cols j).val/p:ℕ):ℤ)) := by
  unfold selectedFactorialCost
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    rw [OddZeta.Coefficients.factorial_valuation_below_square p _
      (target_selected_factorial_lt_square n _ hs)]

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
end OddZeta.FourValue

attribute [instance] DivisionRing.toRatAlgebra

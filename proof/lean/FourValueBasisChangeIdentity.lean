import FourValueActualBasisChange

noncomputable section
namespace OddZeta.FourValue
open Polynomial

def adaptedCoefficientMatrix (n : ℕ) :=
  polynomialCoefficientMatrix (targetHankelDegree n) (fun i => actualAdaptedBasis n i.val)
def adaptedMonicCoefficientMatrix (n : ℕ) :=
  polynomialCoefficientMatrix (targetHankelDegree n) (fun i => actualAdaptedMonic n i.val)
def squareMonicCoefficientMatrix (n : ℕ) :=
  polynomialCoefficientMatrix (targetHankelDegree n) (fun i => squareRootProduct (K:=ℂ) i.val)
def basisFactorialMatrix (n : ℕ) :
    Matrix (Fin (targetHankelDegree n+1)) (Fin (targetHankelDegree n+1)) ℂ :=
  Matrix.diagonal (fun i => (Nat.factorial (2*i.val):ℂ))
def squareMultiplierMatrix (n : ℕ) :
    Matrix (Fin (targetHankelDegree n+1)) (Fin (targetHankelDegree n+1)) ℂ :=
  Matrix.diagonal (fun i => squareBasisMultiplier i.val/(Nat.factorial (2*i.val):ℂ))

theorem adaptedCoefficientMatrix_scale (n : ℕ) :
    adaptedCoefficientMatrix n*basisFactorialMatrix n=adaptedMonicCoefficientMatrix n := by
  ext i j
  simp [adaptedCoefficientMatrix,basisFactorialMatrix,adaptedMonicCoefficientMatrix,
    polynomialCoefficientMatrix,Matrix.mul_diagonal,actualAdaptedMonic,coeff_C_mul,mul_comm]

theorem squareMonicCoefficientMatrix_scale (n : ℕ) :
    squareMonicCoefficientMatrix n*squareMultiplierMatrix n=squareBasisMatrix (K:=ℂ) (targetHankelDegree n) := by
  ext i j
  simp only [squareMonicCoefficientMatrix,squareMultiplierMatrix,Matrix.mul_diagonal,
    polynomialCoefficientMatrix,squareBasisMatrix]
  by_cases hj : j.val=0
  · simp [squareBasisPolynomial,squareBasisMultiplier,hj,squareRootProduct,linearRootProduct]
  · simp [squareBasisPolynomial,squareBasisMultiplier,hj,coeff_C_mul,mul_comm]

theorem adaptedToSquare_matrix (n : ℕ) :
    adaptedToSquare n=basisFactorialMatrix n*
      ((adaptedMonicCoefficientMatrix n)⁻¹*squareMonicCoefficientMatrix n)*squareMultiplierMatrix n := by
  ext i j
  simp only [adaptedToSquare,basisFactorialMatrix,squareMultiplierMatrix,Matrix.diagonal_mul,
    Matrix.mul_diagonal,adaptedMonicTransition,monicBasisTransition,
    adaptedMonicCoefficientMatrix,squareMonicCoefficientMatrix]

theorem adaptedCoefficientMatrix_change (n : ℕ) (hn : 1≤n) :
    adaptedCoefficientMatrix n*adaptedToSquare n=squareBasisMatrix (K:=ℂ) (targetHankelDegree n) := by
  have hd : (adaptedMonicCoefficientMatrix n).det=1 :=
    monicCoefficientMatrix_det _ (fun i => actualAdaptedMonic_monic n i.val hn (by omega))
      (fun i => actualAdaptedMonic_natDegree n i.val hn (by omega))
  have hu : IsUnit (adaptedMonicCoefficientMatrix n).det := by rw [hd]; exact isUnit_one
  rw [adaptedToSquare_matrix]
  calc
    _ = (adaptedCoefficientMatrix n*basisFactorialMatrix n)*(adaptedMonicCoefficientMatrix n)⁻¹*
        squareMonicCoefficientMatrix n*squareMultiplierMatrix n := by simp only [Matrix.mul_assoc]
    _ = squareMonicCoefficientMatrix n*squareMultiplierMatrix n := by
      rw [adaptedCoefficientMatrix_scale,Matrix.mul_nonsing_inv _ hu,Matrix.one_mul]
    _ = _ := squareMonicCoefficientMatrix_scale n

theorem analyticZetaMatrix_change_of_basis (n : ℕ) (hn : 1≤n) :
    analyticZetaMatrix n=(adaptedToSquare n).transpose*actualAdaptedZetaMatrix n*adaptedToSquare n := by
  have hQ := momentGram_change_of_basis (analyticZetaFunctional n) (targetHankelDegree n)
    (fun i => actualAdaptedBasis n i.val) (fun i => by rw [actualAdaptedBasis_natDegree n i.val hn (by omega)]; omega)
  have hE := momentGram_change_of_basis (analyticZetaFunctional n) (targetHankelDegree n)
    (fun i => squareBasisPolynomial i.val) (fun i => by rw [squareBasisPolynomial_degree]; omega)
  change actualAdaptedZetaMatrix n=(adaptedCoefficientMatrix n).transpose*
    momentHankel (analyticZetaFunctional n) (targetHankelDegree n)*adaptedCoefficientMatrix n at hQ
  change analyticZetaMatrix n=(squareBasisMatrix (K:=ℂ) (targetHankelDegree n)).transpose*
    momentHankel (analyticZetaFunctional n) (targetHankelDegree n)*squareBasisMatrix (targetHankelDegree n) at hE
  rw [hQ,hE,← adaptedCoefficientMatrix_change n hn,Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
end OddZeta.FourValue

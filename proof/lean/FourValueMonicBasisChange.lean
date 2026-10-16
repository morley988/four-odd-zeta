import FourValueWeightedTriangular
import FourValueRootCoefficientBounds

noncomputable section
namespace OddZeta.FourValue
open Polynomial

theorem upper_triangular_product_bound {m : ℕ}
    (A B : Matrix (Fin (m+1)) (Fin (m+1)) ℂ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular)
    (C : ℝ) (hC : 0≤C)
    (hAb : ∀ i j,i≤j → ‖A i j‖≤C^(j.val-i.val))
    (hBb : ∀ i j,i≤j → ‖B i j‖≤C^(j.val-i.val)) (i j : Fin (m+1)) (hij : i≤j) :
    ‖(A*B) i j‖≤((m+1:ℕ):ℝ)*C^(j.val-i.val) := by
  classical
  rw [Matrix.mul_apply]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k : Fin (m+1),C^(j.val-i.val) := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hik : i≤k
      · by_cases hkj : k≤j
        · rw [norm_mul]
          calc
            _ ≤ C^(k.val-i.val)*C^(j.val-k.val) :=
              mul_le_mul (hAb _ _ hik) (hBb _ _ hkj) (norm_nonneg _) (pow_nonneg hC _)
            _ = _ := by rw [← pow_add]; congr 1; omega
        · rw [hB (lt_of_not_ge hkj),mul_zero,norm_zero]; positivity
      · rw [hA (lt_of_not_ge hik),zero_mul,norm_zero]; positivity
    _ = _ := by simp

theorem monicCoefficientMatrix_triangular {m : ℕ} (P : Fin (m+1)→ℂ[X])
    (hd : ∀ i,(P i).natDegree=i.val) : (polynomialCoefficientMatrix m P).IsUpperTriangular := by
  intro i j hij
  change (P j).coeff i.val=0
  apply coeff_eq_zero_of_natDegree_lt
  rw [hd]
  exact hij

theorem monicCoefficientMatrix_diagonal {m : ℕ} (P : Fin (m+1)→ℂ[X])
    (hP : ∀ i,(P i).Monic) (hd : ∀ i,(P i).natDegree=i.val) (i : Fin (m+1)) :
    polynomialCoefficientMatrix m P i i=1 := by
  change (P i).coeff i.val=1
  have hc := coeff_natDegree (p:=P i)
  rw [hd] at hc
  rw [hc,(hP i).leadingCoeff]

theorem monicCoefficientMatrix_det {m : ℕ} (P : Fin (m+1)→ℂ[X])
    (hP : ∀ i,(P i).Monic) (hd : ∀ i,(P i).natDegree=i.val) :
    (polynomialCoefficientMatrix m P).det=1 := by
  rw [Matrix.det_of_isUpperTriangular (monicCoefficientMatrix_triangular P hd)]
  simp [monicCoefficientMatrix_diagonal P hP hd]

theorem monicCoefficientMatrix_bound {m : ℕ} (P : Fin (m+1)→ℂ[X])
    (hP : ∀ i,(P i).Monic) (hd : ∀ i,(P i).natDegree=i.val)
    (R : ℝ) (hR : 0≤R) (hroot : ∀ i z,(P i).eval z=0 → ‖z‖≤R)
    (i j : Fin (m+1)) (hij : i≤j) :
    ‖polynomialCoefficientMatrix m P i j‖≤(((m+1:ℕ):ℝ)*R)^(j.val-i.val) := by
  have h := monic_root_coefficient_power_bound (P j) (hP j) R hR (hroot j)
    (m+1) i.val (by rw [hd]; omega) (by rw [hd]; exact hij)
  simpa only [polynomialCoefficientMatrix,hd] using h

def monicBasisTransition {m : ℕ} (P Q : Fin (m+1)→ℂ[X]) :
    Matrix (Fin (m+1)) (Fin (m+1)) ℂ :=
  (polynomialCoefficientMatrix m P)⁻¹*polynomialCoefficientMatrix m Q

theorem monicBasisTransition_triangular {m : ℕ} (P Q : Fin (m+1)→ℂ[X])
    (hP : ∀ i,(P i).Monic) (hdP : ∀ i,(P i).natDegree=i.val)
    (hdQ : ∀ i,(Q i).natDegree=i.val) : (monicBasisTransition P Q).IsUpperTriangular := by
  have hu : IsUnit (polynomialCoefficientMatrix m P).det := by
    rw [monicCoefficientMatrix_det P hP hdP]; exact isUnit_one
  letI := Matrix.invertibleOfIsUnitDet (polynomialCoefficientMatrix m P) hu
  exact (Matrix.blockTriangular_inv_of_blockTriangular (monicCoefficientMatrix_triangular P hdP)).mul
    (monicCoefficientMatrix_triangular Q hdQ)

theorem monicBasisTransition_bound {m : ℕ} (P Q : Fin (m+1)→ℂ[X])
    (hP : ∀ i,(P i).Monic) (hQ : ∀ i,(Q i).Monic)
    (hdP : ∀ i,(P i).natDegree=i.val) (hdQ : ∀ i,(Q i).natDegree=i.val)
    (R : ℝ) (hR : 0<R)
    (hrP : ∀ i z,(P i).eval z=0 → ‖z‖≤R) (hrQ : ∀ i z,(Q i).eval z=0 → ‖z‖≤R)
    (i j : Fin (m+1)) (hij : i≤j) :
    ‖monicBasisTransition P Q i j‖≤((m+1:ℕ):ℝ)*(((m+1:ℕ):ℝ)^2*R)^(j.val-i.val) := by
  let C : ℝ := ((m+1:ℕ):ℝ)*R
  have hC : 0<C := by dsimp [C]; positivity
  have hp := monicCoefficientMatrix_triangular P hdP
  have hq := monicCoefficientMatrix_triangular Q hdQ
  have hu : IsUnit (polynomialCoefficientMatrix m P).det := by
    rw [monicCoefficientMatrix_det P hP hdP]; exact isUnit_one
  letI := Matrix.invertibleOfIsUnitDet (polynomialCoefficientMatrix m P) hu
  have hp' := Matrix.blockTriangular_inv_of_blockTriangular hp
  have hb := unitUpper_inverse_weighted_bound (polynomialCoefficientMatrix m P) hp
    (monicCoefficientMatrix_diagonal P hP hdP) C hC (monicCoefficientMatrix_bound P hP hdP R hR.le hrP)
  have hD : ((m+1:ℕ):ℝ)*C=((m+1:ℕ):ℝ)^2*R := by dsimp [C]; ring
  have hq' : ∀ i j,i≤j → ‖polynomialCoefficientMatrix m Q i j‖≤(((m+1:ℕ):ℝ)*C)^(j.val-i.val) := by
    intro i j hij
    apply (monicCoefficientMatrix_bound Q hQ hdQ R hR.le hrQ i j hij).trans
    apply pow_le_pow_left₀ hC.le
    have hn : (1:ℝ)≤(m+1:ℕ) := by exact_mod_cast (show 1≤m+1 by omega)
    nlinarith
  have h := upper_triangular_product_bound _ _ hp' hq (((m+1:ℕ):ℝ)*C) (by positivity) hb hq' i j hij
  simpa only [monicBasisTransition,hD] using h
end OddZeta.FourValue

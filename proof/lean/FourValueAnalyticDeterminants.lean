import FourValueScaledBasisBounds

noncomputable section
namespace OddZeta.FourValue
open Polynomial

theorem complex_det_bound {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ)
    (u v : Fin k→ℝ) (hu : ∀ i,0≤u i) (hv : ∀ j,0≤v j)
    (hA : ∀ i j,‖A i j‖≤u i*v j) :
    ‖A.det‖≤(Nat.factorial k:ℝ)*(∏ i,u i)*(∏ j,v j) := by
  classical
  rw [Matrix.det_apply]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin k), (∏ i,u i)*(∏ j,v j) := by
      apply Finset.sum_le_sum
      intro σ _
      have hs : ‖Equiv.Perm.sign σ • ∏ i,A (σ i) i‖=‖∏ i,A (σ i) i‖ := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h|h <;> simp [h]
      rw [hs,norm_prod]
      calc
        _ ≤ ∏ i,u (σ i)*v i := Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hA _ _)
        _ = _ := by rw [Finset.prod_mul_distrib,Equiv.prod_comp]
    _ = _ := by simp [Fintype.card_perm,mul_assoc]

theorem complex_det_uniform_bound {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ)
    (B : ℝ) (hB : 0≤B) (hA : ∀ i j,‖A i j‖≤B) :
    ‖A.det‖≤(Nat.factorial k:ℝ)*B^k := by
  simpa using complex_det_bound A (fun _ => B) (fun _ => 1) (fun _ => hB)
    (fun _ => by norm_num) (by simpa using hA)

def scaledAnalyticCoefficientMatrix (M : ℝ) (m : ℕ) (w : Fin (m+1)→Fin 45→ℝ) :
    Matrix (Fin (m+1)) (Fin (m+1)) ℂ :=
  polynomialCoefficientMatrix m (fun i => scaledAnalyticBasis M i.val (w i))

theorem scaledAnalyticCoefficientMatrix_triangular (M : ℝ) (hM : M≠0) (m : ℕ)
    (w : Fin (m+1)→Fin 45→ℝ) (hw : ∀ i l,0≤w i l) (hs : ∀ i,∑ l,w i l=1) :
    (scaledAnalyticCoefficientMatrix M m w).IsUpperTriangular := by
  intro i j hij
  change (scaledAnalyticBasis M j.val (w j)).coeff i.val=0
  apply coeff_eq_zero_of_natDegree_lt
  rw [scaledAnalyticBasis_natDegree M hM j.val (w j) (hw j) (hs j)]
  exact hij

theorem scaledAnalyticCoefficientMatrix_det (M : ℝ) (hM : M≠0) (m : ℕ)
    (w : Fin (m+1)→Fin 45→ℝ) (hw : ∀ i l,0≤w i l) (hs : ∀ i,∑ l,w i l=1) :
    (scaledAnalyticCoefficientMatrix M m w).det=
      ∏ i : Fin (m+1),1/(Nat.factorial (2*i.val):ℂ) := by
  rw [Matrix.det_of_isUpperTriangular (scaledAnalyticCoefficientMatrix_triangular M hM m w hw hs)]
  apply Finset.prod_congr rfl
  intro i _
  change (scaledAnalyticBasis M i.val (w i)).coeff i.val=_
  have hd := scaledAnalyticBasis_natDegree M hM i.val (w i) (hw i) (hs i)
  have hc := coeff_natDegree (p:=scaledAnalyticBasis M i.val (w i))
  rw [hd] at hc
  rw [hc,scaledAnalyticBasis_leadingCoeff M hM i.val (w i) (hw i) (hs i)]

theorem scaledAnalyticCoefficientMatrix_det_ne_zero (M : ℝ) (hM : M≠0) (m : ℕ)
    (w : Fin (m+1)→Fin 45→ℝ) (hw : ∀ i l,0≤w i l) (hs : ∀ i,∑ l,w i l=1) :
    (scaledAnalyticCoefficientMatrix M m w).det≠0 := by
  rw [scaledAnalyticCoefficientMatrix_det M hM m w hw hs]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
end OddZeta.FourValue

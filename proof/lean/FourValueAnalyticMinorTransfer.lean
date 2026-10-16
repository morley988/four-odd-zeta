import FourValueBasisChangeIdentity

noncomputable section
namespace OddZeta.FourValue

theorem complex_det_submatrix_noninjective {k d : ℕ} (A : Matrix (Fin k) (Fin d) ℂ)
    (f : Fin k→Fin d) (hf : ¬Function.Injective f) : (A.submatrix id f).det=0 := by
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hf
  apply Matrix.det_zero_of_column_eq hne
  intro l
  simp [hij]

theorem upper_triangular_selected_product_bound {m k : ℕ}
    (T : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) (hT : T.IsUpperTriangular)
    (B D : ℝ) (hB : 0≤B) (hD : 1≤D)
    (ht : ∀ i j,i≤j → ‖T i j‖≤B*D^(j.val-i.val))
    (r c : Fin k ↪ Fin (m+1)) :
    ‖∏ i,T (r i) (c i)‖≤B^k*D^((m+1-k)*m) := by
  classical
  rw [norm_prod]
  by_cases hle : ∀ i,r i≤c i
  · calc
      _ ≤ ∏ i,B*D^((c i).val-(r i).val) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ht _ _ (hle i))
      _ = B^k*D^((∑ i,(c i).val)-(∑ i,(r i).val)) := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Finset.prod_pow_eq_pow_sum]
        have hsub : (∑ i, ((c i).val-(r i).val))=(∑ i,(c i).val)-(∑ i,(r i).val) :=
          Finset.sum_tsub_distrib _ (fun i _ => hle i)
        rw [hsub]
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (selected_sum_difference_bound r c)) (pow_nonneg hB _)
  · push Not at hle
    obtain ⟨i,hi⟩ := hle
    have hz : ∏ j : Fin k,‖T (r j) (c j)‖=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hT hi,norm_zero]
    rw [hz]
    positivity

def triangularTransferFactor (m k : ℕ) (B D : ℝ) : ℝ :=
  ((m+1:ℕ):ℝ)^k*B^k*D^((m+1-k)*m)

theorem complex_det_right_triangular_transfer {m k : ℕ}
    (A : Matrix (Fin k) (Fin (m+1)) ℂ)
    (T : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) (hT : T.IsUpperTriangular)
    (B D H : ℝ) (hB : 0≤B) (hD : 1≤D) (hH : 0≤H)
    (ht : ∀ i j,i≤j → ‖T i j‖≤B*D^(j.val-i.val))
    (hA : ∀ f : Fin k ↪ Fin (m+1),‖(A.submatrix id f).det‖≤H)
    (c : Fin k ↪ Fin (m+1)) :
    ‖(A*T.submatrix id c).det‖≤H*triangularTransferFactor m k B D := by
  classical
  rw [det_rectangular_expansion]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ f : Fin k→Fin (m+1),H*(B^k*D^((m+1-k)*m)) := by
      apply Finset.sum_le_sum
      intro f _
      by_cases hf : Function.Injective f
      · rw [norm_mul]
        apply mul_le_mul (hA ⟨f,hf⟩) _ (norm_nonneg _) hH
        exact upper_triangular_selected_product_bound T hT B D hB hD ht ⟨f,hf⟩ c
      · rw [complex_det_submatrix_noninjective A f hf,zero_mul,norm_zero]
        positivity
    _ = _ := by simp [triangularTransferFactor,Fintype.card_fun]; ring

theorem complex_gram_triangular_transfer {m k : ℕ}
    (A T : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) (hT : T.IsUpperTriangular)
    (B D H : ℝ) (hB : 0≤B) (hD : 1≤D) (hH : 0≤H)
    (ht : ∀ i j,i≤j → ‖T i j‖≤B*D^(j.val-i.val))
    (hA : ∀ r c : Fin k ↪ Fin (m+1),‖(A.submatrix r c).det‖≤H)
    (r c : Fin k ↪ Fin (m+1)) :
    ‖((T.transpose*A*T).submatrix r c).det‖≤H*(triangularTransferFactor m k B D)^2 := by
  classical
  let U := (T.submatrix id r).transpose*A
  have hU : ∀ f : Fin k ↪ Fin (m+1),‖(U.submatrix id f).det‖≤H*triangularTransferFactor m k B D := by
    intro f
    have he : (U.submatrix id f).transpose=(A.submatrix id f).transpose*T.submatrix id r := by
      ext i j
      simp [U,Matrix.mul_apply,Matrix.transpose_apply,Matrix.submatrix_apply,mul_comm]
    rw [← Matrix.det_transpose,he]
    apply complex_det_right_triangular_transfer _ T hT B D H hB hD hH ht _ r
    intro g
    have he' : ((A.submatrix id f).transpose.submatrix id g)=(A.submatrix g f).transpose := rfl
    rw [he',Matrix.det_transpose]
    exact hA g f
  have he : (T.transpose*A*T).submatrix r c=U*T.submatrix id c := by
    ext i j
    simp [U,Matrix.mul_apply,Matrix.transpose_apply,Matrix.submatrix_apply,mul_comm]
  rw [he]
  have hF : 0≤triangularTransferFactor m k B D := by
    unfold triangularTransferFactor
    have : 0≤D := by linarith
    positivity
  have h := complex_det_right_triangular_transfer U T hT B D
    (H*triangularTransferFactor m k B D) hB hD (mul_nonneg hH hF) ht hU c
  convert h using 1 <;> ring

def actualAnalyticTransferFactor (n : ℕ) : ℝ :=
  triangularTransferFactor (targetHankelDegree n) (targetHankelDegree n+1-4)
    (2*((targetHankelDegree n+1:ℕ):ℝ)) (analyticTransitionBase n)

theorem analyticZetaMatrix_minor_transfer (n : ℕ) (hn : 1≤n) (H : ℝ) (hH : 0≤H)
    (hA : ∀ r c : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1),
      ‖((actualAdaptedZetaMatrix n).submatrix r c).det‖≤H)
    (r c : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1)) :
    ‖((analyticZetaMatrix n).submatrix r c).det‖≤H*(actualAnalyticTransferFactor n)^2 := by
  rw [analyticZetaMatrix_change_of_basis n hn]
  exact complex_gram_triangular_transfer _ _ (adaptedToSquare_triangular n hn) _ _ H
    (by positivity) (analyticTransitionBase_ge_one n hn) hH (adaptedToSquare_bound n hn) hA r c
end OddZeta.FourValue

import FourValueOmittedIndices

noncomputable section
namespace OddZeta.FourValue

theorem upper_triangular_large_minor_bound {m k : ℕ}
    (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) (hA : A.IsUpperTriangular)
    (B D : ℝ) (hB : 0≤B) (hD : 1≤D)
    (hbound : ∀ i j,i≤j → ‖A i j‖≤B*D^(j.val-i.val))
    (r c : Fin k ↪ Fin (m+1)) :
    ‖(A.submatrix r c).det‖≤(Nat.factorial k:ℝ)*B^k*D^((m+1-k)*m) := by
  classical
  rw [Matrix.det_apply]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin k), B^k*D^((m+1-k)*m) := by
      apply Finset.sum_le_sum
      intro σ _
      have hs : ‖Equiv.Perm.sign σ • ∏ i,A (r (σ i)) (c i)‖=‖∏ i,A (r (σ i)) (c i)‖ := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h|h <;> simp [h]
      change ‖Equiv.Perm.sign σ • ∏ i,A (r (σ i)) (c i)‖≤_
      rw [hs,norm_prod]
      by_cases hle : ∀ i,r (σ i)≤c i
      · calc
          _ ≤ ∏ i,B*D^((c i).val-(r (σ i)).val) :=
            Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hbound _ _ (hle i))
          _ = B^k*D^((∑ i,(c i).val)-(∑ i,(r i).val)) := by
            rw [Finset.prod_mul_distrib]
            simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Finset.prod_pow_eq_pow_sum]
            have hsub : (∑ i, ((c i).val-(r (σ i)).val))=(∑ i,(c i).val)-(∑ i,(r (σ i)).val) :=
              Finset.sum_tsub_distrib _ (fun i _ => hle i)
            rw [hsub,Equiv.sum_comp σ (fun i => (r i).val)]
          _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (selected_sum_difference_bound r c))
            (pow_nonneg hB _)
      · push Not at hle
        obtain ⟨i,hi⟩ := hle
        have hz : ∏ j : Fin k,‖A (r (σ j)) (c j)‖=0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          rw [hA hi,norm_zero]
        rw [hz]
        positivity
    _ = _ := by simp [Fintype.card_perm,mul_assoc]

theorem upper_triangular_four_omitted_bound {m : ℕ}
    (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) (hA : A.IsUpperTriangular)
    (B D : ℝ) (hB : 0≤B) (hD : 1≤D)
    (hbound : ∀ i j,i≤j → ‖A i j‖≤B*D^(j.val-i.val))
    (r c : Fin (m+1-4) ↪ Fin (m+1)) :
    ‖(A.submatrix r c).det‖≤(Nat.factorial (m+1-4):ℝ)*B^(m+1-4)*D^(4*m) := by
  apply (upper_triangular_large_minor_bound A hA B D hB hD hbound r c).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_right₀ hD (Nat.mul_le_mul_right m (by omega))
end OddZeta.FourValue

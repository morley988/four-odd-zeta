import FourValueAnalyticDeterminants

noncomputable section
namespace OddZeta.FourValue

/-- A concrete inverse estimate retaining the distance above the diagonal. -/
theorem upper_triangular_inverse_entry_bound {m : ℕ}
    (A B : Matrix (Fin (m+1)) (Fin (m+1)) ℂ)
    (hAB : A*B=1) (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular)
    (hdiag : ∀ i,A i i=1) (hentry : ∀ i j,‖A i j‖≤1) :
    ∀ i j, i≤j → ‖B i j‖≤((m+1:ℕ):ℝ)^(j.val-i.val) := by
  classical
  intro i j hij
  generalize hd : j.val-i.val=d
  induction d using Nat.strong_induction_on generalizing i j with
  | h d ih =>
    have he := congrArg (fun M : Matrix (Fin (m+1)) (Fin (m+1)) ℂ => M i j) hAB
    rw [Matrix.mul_apply,← Finset.sum_erase_add _ _ (Finset.mem_univ i),hdiag i,one_mul] at he
    by_cases heq : i=j
    · subst j
      have hz : ∑ k∈Finset.univ.erase i,A i k*B k i=0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hki : k≠i := (Finset.mem_erase.mp hk).1
        rcases lt_or_gt_of_ne hki with hk|hk
        · rw [hA hk,zero_mul]
        · rw [hB hk,mul_zero]
      rw [hz,zero_add] at he
      have hd0 : d=0 := by omega
      simp [he,hd0]
    · have hlt : i<j := lt_of_le_of_ne hij heq
      have hdpos : 0<d := by omega
      have hz : (1:Matrix (Fin (m+1)) (Fin (m+1)) ℂ) i j=0 := Matrix.one_apply_ne heq
      rw [hz] at he
      have heB : B i j= -(∑ k∈Finset.univ.erase i,A i k*B k j) := by linear_combination he
      rw [heB,norm_neg]
      apply (norm_sum_le _ _).trans
      have hpow : 1≤((m+1:ℕ):ℝ) := by exact_mod_cast (show 1≤m+1 by omega)
      calc
        _ ≤ ∑ k∈Finset.univ.erase i, ((m+1:ℕ):ℝ)^(d-1) := by
          apply Finset.sum_le_sum
          intro k hk
          have hki : k≠i := (Finset.mem_erase.mp hk).1
          by_cases hik : i<k
          · by_cases hkj : k≤j
            · have hdlt : j.val-k.val<d := by omega
              have hib := ih _ hdlt k j hkj rfl
              rw [norm_mul]
              calc
                _ ≤ 1*(((m+1:ℕ):ℝ)^(j.val-k.val)) :=
                  mul_le_mul (hentry i k) hib (norm_nonneg _) (by norm_num)
                _ ≤ _ := by rw [one_mul]; exact pow_le_pow_right₀ hpow (by omega)
            · rw [hB (lt_of_not_ge hkj),mul_zero,norm_zero]
              positivity
          · have hki' : k < i := lt_of_le_of_ne (le_of_not_gt hik) hki
            rw [hA hki',zero_mul,norm_zero]
            positivity
        _ ≤ ((m+1:ℕ):ℝ)*((m+1:ℕ):ℝ)^(d-1) := by
          rw [Finset.sum_const,nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast (Finset.card_erase_le.trans (show Finset.univ.card≤m+1 by simp))
        _ = _ := by rw [← pow_succ',Nat.sub_add_cancel hdpos]
end OddZeta.FourValue

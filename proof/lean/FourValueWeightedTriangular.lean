import FourValueTriangularBounds

noncomputable section
namespace OddZeta.FourValue

def triangularRescale {m : ℕ} (C : ℝ) (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) :
    Matrix (Fin (m+1)) (Fin (m+1)) ℂ := fun i j => (C:ℂ)^i.val*A i j/(C:ℂ)^j.val

theorem triangularRescale_mul {m : ℕ} (C : ℝ) (hC : C≠0)
    (A B : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) :
    triangularRescale C (A*B)=triangularRescale C A*triangularRescale C B := by
  have hCc : (C:ℂ)≠0 := by exact_mod_cast hC
  ext i j
  simp only [triangularRescale,Matrix.mul_apply,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  field_simp

theorem triangularRescale_one {m : ℕ} (C : ℝ) (hC : C≠0) :
    triangularRescale C (1:Matrix (Fin (m+1)) (Fin (m+1)) ℂ)=1 := by
  have hCc : (C:ℂ)≠0 := by exact_mod_cast hC
  ext i j
  by_cases hij : i=j
  · subst j
    simp [triangularRescale,hCc]
  · simp [triangularRescale,Matrix.one_apply_ne hij]

theorem triangularRescale_triangular {m : ℕ} (C : ℝ)
    (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) (hA : A.IsUpperTriangular) :
    (triangularRescale C A).IsUpperTriangular := by
  intro i j hij
  simp [triangularRescale,hA hij]

theorem triangularRescale_norm {m : ℕ} (C : ℝ) (hC : 0<C)
    (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) (i j : Fin (m+1)) :
    ‖triangularRescale C A i j‖=C^i.val*‖A i j‖/C^j.val := by
  simp [triangularRescale,norm_div,norm_mul,norm_pow,abs_of_pos hC]

theorem triangularRescale_entry_le_one {m : ℕ} (C : ℝ) (hC : 0<C)
    (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) (hA : A.IsUpperTriangular)
    (hbound : ∀ i j,i≤j → ‖A i j‖≤C^(j.val-i.val)) (i j : Fin (m+1)) :
    ‖triangularRescale C A i j‖≤1 := by
  by_cases hij : i≤j
  · rw [triangularRescale_norm C hC,div_le_one (pow_pos hC _)]
    calc
      _ ≤ C^i.val*C^(j.val-i.val) := mul_le_mul_of_nonneg_left (hbound i j hij) (pow_nonneg hC.le _)
      _ = _ := by rw [← pow_add,Nat.add_sub_of_le hij]
  · simp [triangularRescale,hA (lt_of_not_ge hij)]

theorem unitUpper_inverse_weighted_bound {m : ℕ}
    (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) (hA : A.IsUpperTriangular)
    (hdiag : ∀ i,A i i=1) (C : ℝ) (hC : 0<C)
    (hbound : ∀ i j,i≤j → ‖A i j‖≤C^(j.val-i.val)) :
    ∀ i j,i≤j → ‖A⁻¹ i j‖≤(((m+1:ℕ):ℝ)*C)^(j.val-i.val) := by
  classical
  have hd : A.det=1 := by rw [Matrix.det_of_isUpperTriangular hA]; simp [hdiag]
  have hunit : IsUnit A.det := by rw [hd]; exact isUnit_one
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A hunit
  have hB : A⁻¹.IsUpperTriangular := Matrix.blockTriangular_inv_of_blockTriangular hA
  have hab : triangularRescale C A*triangularRescale C A⁻¹=1 := by
    rw [← triangularRescale_mul C hC.ne',Matrix.mul_nonsing_inv A hunit,triangularRescale_one C hC.ne']
  have hdiag' : ∀ i,triangularRescale C A i i=1 := by
    intro i
    have hCc : (C:ℂ)≠0 := by exact_mod_cast hC.ne'
    simp [triangularRescale,hdiag,hCc]
  intro i j hij
  have hb := upper_triangular_inverse_entry_bound (triangularRescale C A) (triangularRescale C A⁻¹)
    hab (triangularRescale_triangular C A hA) (triangularRescale_triangular C A⁻¹ hB)
    hdiag' (triangularRescale_entry_le_one C hC A hA hbound) i j hij
  rw [triangularRescale_norm C hC] at hb
  rw [div_le_iff₀ (pow_pos hC _)] at hb
  have he : C^j.val=C^i.val*C^(j.val-i.val) := by rw [← pow_add,Nat.add_sub_of_le hij]
  rw [he] at hb
  rw [mul_pow]
  nlinarith [pow_pos hC i.val]
end OddZeta.FourValue

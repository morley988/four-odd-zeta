import FourValueResidueFloors

noncomputable section
namespace OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

/-- Integral column combinations preserve a uniform bound on all minors. -/
theorem padicLower_det_right_integral {k d : ℕ}
    (A : Matrix (Fin k) (Fin d) ℚ) (B : Matrix (Fin d) (Fin k) ℚ) (w : ℤ)
    (hA : ∀ f : Fin k → Fin d, PadicLower p w (A.submatrix id f).det)
    (hB : ∀ i j, PadicLower p 0 (B i j)) : PadicLower p w (A*B).det := by
  rw [det_rectangular_expansion]
  apply padicLower_sum
  intro f hf
  have hb := padicLower_prod (p:=p) Finset.univ (fun i => B (f i) i) (fun _ => (0:ℤ))
    (fun i hi => hB (f i) i)
  simpa using (hA f).mul hb

theorem padicLower_det_left_integral {k d : ℕ}
    (A : Matrix (Fin k) (Fin d) ℚ) (B : Matrix (Fin d) (Fin k) ℚ) (w : ℤ)
    (hA : ∀ i j, PadicLower p 0 (A i j))
    (hB : ∀ f : Fin k → Fin d, PadicLower p w (B.submatrix f id).det) :
    PadicLower p w (A*B).det := by
  have h := padicLower_det_right_integral B.transpose A.transpose w
    (fun f => by simpa only [← Matrix.transpose_submatrix, Matrix.det_transpose] using hB f)
    (fun i j => hA j i)
  simpa only [← Matrix.transpose_mul, Matrix.det_transpose] using h

/-- A valuation version of the rectangular determinant expansion, with
independent integer changes of row and column polynomial families. -/
theorem padicLower_det_integral_change {k d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (U : Matrix (Fin k) (Fin d) ℚ)
    (V : Matrix (Fin d) (Fin k) ℚ) (w : ℤ)
    (hA : ∀ rows cols : Fin k → Fin d, PadicLower p w (A.submatrix rows cols).det)
    (hU : ∀ i j, PadicLower p 0 (U i j)) (hV : ∀ i j, PadicLower p 0 (V i j)) :
    PadicLower p w (U*A*V).det := by
  apply padicLower_det_right_integral _ V w _ hV
  intro cols
  have he : (U*A).submatrix id cols = U*(A.submatrix id cols) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [he]
  apply padicLower_det_left_integral U _ w hU
  intro rows
  simpa [Matrix.submatrix_submatrix, Function.comp_def] using hA rows cols

theorem matrix_submatrix_det_zero_of_not_injective {k d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (rows cols : Fin k → Fin d)
    (h : ¬Function.Injective rows ∨ ¬Function.Injective cols) :
    (A.submatrix rows cols).det = 0 := by
  rcases h with h | h
  · obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp h
    apply Matrix.det_zero_of_row_eq hne
    funext l
    simp [hij]
  · obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp h
    apply Matrix.det_zero_of_column_eq hne
    intro l
    simp [hij]

/-- Concrete paired residue-class bounds survive every integral matrix
change of polynomial coordinates, including non-principal minors. -/
theorem pairedResidueClass_integral_change_bound (n b : ℕ) (S : Finset ℤ) (r : ℤ)
    (lambda : Fin 4 → ℚ) {k d : ℕ}
    (U : Matrix (Fin k) (Fin d) ℚ) (V : Matrix (Fin d) (Fin k) ℚ)
    (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda)
    (hS : ∀ a∈S, a∈poleWindow (100*n) ∧ ((p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) ∧ (b-a).toNat<p^2)
    (hU : ∀ i j, PadicLower p 0 (U i j)) (hV : ∀ i j, PadicLower p 0 (V i j)) :
    PadicLower p ((k:ℤ)^2+(targetLocalWeight p n r-5)*k)
      (U*residueClassMatrix n b S r lambda Fin.val Fin.val*V).det := by
  apply padicLower_det_integral_change _ U V _ _ hU hV
  intro rows cols
  by_cases hr : Function.Injective rows
  · by_cases hc : Function.Injective cols
    · have h := pairedResidueClassMatrix_det_padicLower n b S r lambda
        (fun i => (rows i).val) (fun j => (cols j).val)
        (Fin.val_injective.comp hr) (Fin.val_injective.comp hc) hs hp hS
      exact h
    · rw [matrix_submatrix_det_zero_of_not_injective _ _ _ (Or.inr hc)]
      exact PadicLower.zero _
  · rw [matrix_submatrix_det_zero_of_not_injective _ _ _ (Or.inl hr)]
    exact PadicLower.zero _
/-- Concrete paired residue-class bounds survive every integral matrix
change of polynomial coordinates, including non-principal minors. -/
theorem pairedResidueClass_integral_change_bound_good (n b : ℕ) (S : Finset ℤ) (r : ℤ)
    (lambda : Fin 4 → ℚ) {k d : ℕ}
    (U : Matrix (Fin k) (Fin d) ℚ) (V : Matrix (Fin d) (Fin k) ℚ)
    (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda)
    (hS : ∀ a∈S, a∈poleWindow (100*n) ∧ ((p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) ∧ (b-a).toNat<p)
    (hU : ∀ i j, PadicLower p 0 (U i j)) (hV : ∀ i j, PadicLower p 0 (V i j)) :
    PadicLower p ((k:ℤ)^2+targetLocalWeight p n r*k)
      (U*residueClassMatrix n b S r lambda Fin.val Fin.val*V).det := by
  apply padicLower_det_integral_change _ U V _ _ hU hV
  intro rows cols
  by_cases hr : Function.Injective rows
  · by_cases hc : Function.Injective cols
    · have h := pairedResidueClassMatrix_det_padicLower_good n b S r lambda
        (fun i => (rows i).val) (fun j => (cols j).val)
        (Fin.val_injective.comp hr) (Fin.val_injective.comp hc) hs hp hS
      exact h
    · rw [matrix_submatrix_det_zero_of_not_injective _ _ _ (Or.inr hc)]
      exact PadicLower.zero _
  · rw [matrix_submatrix_det_zero_of_not_injective _ _ _ (Or.inl hr)]
    exact PadicLower.zero _
end OddZeta.FourValue

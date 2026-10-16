import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! Nonzero minors can be selected from a rank bound.  Rows and columns are
selected independently; no principal-minor assertion is made. -/

noncomputable section
namespace OddZeta.FourValue
open Matrix Finset
variable {K : Type*} [Field K]

/-- Expand a determinant of a rectangular product by its column choices.
Noninjective choices automatically have zero determinant. -/
theorem det_rectangular_expansion {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) K) (B : Matrix (Fin n) (Fin k) K) :
    (A * B).det = ∑ f : Fin k → Fin n,
      (A.submatrix id f).det * ∏ i, B (f i) i := by
  classical
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
    Finset.mul_sum, Fintype.piFinset_univ, Matrix.submatrix_apply, id_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.prod_mul_distrib, mul_assoc]

theorem nonzero_product_has_column_minor {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) K) (B : Matrix (Fin n) (Fin k) K)
    (h : (A * B).det ≠ 0) :
    ∃ f : Fin k → Fin n, (A.submatrix id f).det ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  apply h
  rw [det_rectangular_expansion]
  simp [hn]

theorem nonzero_product_has_row_minor {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) K) (B : Matrix (Fin n) (Fin k) K)
    (h : (A * B).det ≠ 0) :
    ∃ f : Fin k → Fin n, (B.submatrix f id).det ≠ 0 := by
  have ht : (B.transpose * A.transpose).det ≠ 0 := by
    simpa only [← Matrix.transpose_mul, Matrix.det_transpose] using h
  obtain ⟨f, hf⟩ := nonzero_product_has_column_minor B.transpose A.transpose ht
  exact ⟨f, by simpa only [← Matrix.transpose_submatrix, Matrix.det_transpose] using hf⟩

/-- A rank lower bound gives an actual square submatrix with nonzero
determinant. The chosen row and column maps are independent. -/
theorem rank_selects_nonzero_minor_maps {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hk : k ≤ A.rank) :
    ∃ r c : Fin k → Fin n, (A.submatrix r c).det ≠ 0 := by
  classical
  obtain ⟨V, U, e, _, _, hnormal⟩ := Matrix.exists_rank_normal_form A
  let t : Fin k → Fin n := fun i => e.symm (Sum.inl (Fin.castLE hk i))
  have hblock : (V * A * U).submatrix t t = (1 : Matrix (Fin k) (Fin k) K) := by
    rw [hnormal]
    ext i j
    simp [t, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
  have hmul : (V.submatrix t id * A * U.submatrix id t).det ≠ 0 := by
    have heq := Matrix.submatrix_mul (V * A) U t id t Function.bijective_id
    rw [Matrix.submatrix_mul V A t id id Function.bijective_id,
      Matrix.submatrix_id_id] at heq
    rw [← heq, hblock, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨c, hc⟩ := nonzero_product_has_column_minor
    (V.submatrix t id * A) (U.submatrix id t) hmul
  rw [Matrix.submatrix_mul _ A id id c Function.bijective_id,
    Matrix.submatrix_id_id] at hc
  obtain ⟨r, hr⟩ := nonzero_product_has_row_minor
    (V.submatrix t id) (A.submatrix id c) hc
  exact ⟨r, c, by simpa only [Matrix.submatrix_submatrix,
    Function.comp_id, Function.id_comp] using hr⟩

/-- Nonzero determinant forces both selection maps to be injective, so the
result above selects genuine row and column sets. -/
theorem rank_selects_nonzero_minor {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hk : k ≤ A.rank) :
    ∃ r c : Fin k ↪ Fin n, (A.submatrix r c).det ≠ 0 := by
  obtain ⟨r, c, h⟩ := rank_selects_nonzero_minor_maps A hk
  have hr : Function.Injective r := by
    intro i j hij
    by_contra hne
    apply h
    apply Matrix.det_zero_of_row_eq hne
    funext l
    simp only [Matrix.submatrix_apply, hij]
  have hc : Function.Injective c := by
    intro i j hij
    by_contra hne
    apply h
    apply Matrix.det_zero_of_column_eq hne
    intro l
    simp only [Matrix.submatrix_apply, hij]
  exact ⟨⟨r, hr⟩, ⟨c, hc⟩, h⟩

end OddZeta.FourValue

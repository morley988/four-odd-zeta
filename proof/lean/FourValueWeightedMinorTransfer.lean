import FourValueArithmeticBoundary

noncomputable section
namespace OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

theorem padicLower_det_right_weighted {k d : ℕ}
    (A : Matrix (Fin k) (Fin d) ℚ) (B : Matrix (Fin d) (Fin k) ℚ) (w : ℤ) (v : Fin k → ℤ)
    (hA : ∀ f : Fin k → Fin d, PadicLower p w (A.submatrix id f).det)
    (hB : ∀ i j, PadicLower p (v j) (B i j)) :
    PadicLower p (w+∑ j,v j) (A*B).det := by
  rw [det_rectangular_expansion]
  apply padicLower_sum
  intro f hf
  exact (hA f).mul (padicLower_prod Finset.univ _ v (fun i hi => hB (f i) i))

theorem padicLower_det_left_weighted {k d : ℕ}
    (A : Matrix (Fin k) (Fin d) ℚ) (B : Matrix (Fin d) (Fin k) ℚ) (w : ℤ) (v : Fin k → ℤ)
    (hA : ∀ i j, PadicLower p (v i) (A i j))
    (hB : ∀ f : Fin k → Fin d, PadicLower p w (B.submatrix f id).det) :
    PadicLower p (w+∑ i,v i) (A*B).det := by
  have h := padicLower_det_right_weighted B.transpose A.transpose w v
    (fun f => by simpa only [← Matrix.transpose_submatrix, Matrix.det_transpose] using hB f)
    (fun i j => hA j i)
  simpa only [← Matrix.transpose_mul, Matrix.det_transpose] using h

theorem padicLower_det_weighted_change {k d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (U : Matrix (Fin k) (Fin d) ℚ)
    (V : Matrix (Fin d) (Fin k) ℚ) (w : ℤ) (u v : Fin k → ℤ)
    (hA : ∀ rows cols : Fin k → Fin d, PadicLower p w (A.submatrix rows cols).det)
    (hU : ∀ i j, PadicLower p (u i) (U i j)) (hV : ∀ i j, PadicLower p (v j) (V i j)) :
    PadicLower p (w+(∑ i,u i)+(∑ j,v j)) (U*A*V).det := by
  apply padicLower_det_right_weighted _ V _ v _ hV
  intro cols
  have he : (U*A).submatrix id cols = U*(A.submatrix id cols) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [he]
  apply padicLower_det_left_weighted U _ w u hU
  intro rows
  simpa [Matrix.submatrix_submatrix, Function.comp_def] using hA rows cols
end OddZeta.FourValue

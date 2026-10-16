import FourValueIntegralMinorTransfer

noncomputable section
namespace OddZeta.FourValue

/-- Under precisely the simultaneous rationality hypothesis, the already
identified derivative-series matrix has a selected nonzero rational minor. -/
theorem classicalZetaSeries_nonzero_rational_minor (n : ℕ) (hn : 1≤n) (z : Fin 4 → ℚ)
    (hz : ∀ i : Fin 4, riemannZeta ((![7,9,11,13] : Fin 4 → ℂ) i) = (z i:ℂ)) :
    ∃ (rows cols : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1))
      (q : ℚ), q≠0 ∧ ((classicalZetaSeriesMatrix n).submatrix rows cols).det = (q:ℂ) := by
  let lambda : Fin 4 → ℚ := fun i => (![15,70,210,495] : Fin 4 → ℚ) i*z i
  obtain ⟨rows,cols,hq⟩ := rationalFourValueMatrix_nonzero_minor n hn lambda
  refine ⟨rows,cols,((rationalFourValueMatrix n lambda).submatrix rows cols).det,hq,?_⟩
  rw [classicalZetaSeriesMatrix_rational n z hz]
  change (((rationalFourValueMatrix n lambda).submatrix rows cols).map (algebraMap ℚ ℂ)).det = _
  convert ((algebraMap ℚ ℂ).map_det
    ((rationalFourValueMatrix n lambda).submatrix rows cols)).symm using 1 <;> rfl

/-- The manuscript's exact noncentral bad-class cost, with both residue
counts and normalization reduced to explicit integer floor expressions. -/
theorem concrete_bad_class_floor_bound {p : ℕ} [Fact p.Prime]
    (n b : ℕ) (S : Finset ℤ) (r : ℤ) (lambda : Fin 4 → ℚ) {k d : ℕ}
    (U : Matrix (Fin k) (Fin d) ℚ) (V : Matrix (Fin d) (Fin k) ℚ)
    (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda) (hr : ¬(p:ℤ)∣r)
    (hS : ∀ a∈S, a∈poleWindow (100*n) ∧ ((p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) ∧ (b-a).toNat<p^2)
    (hU : ∀ i j, PadicLower p 0 (U i j)) (hV : ∀ i j, PadicLower p 0 (V i j)) :
    PadicLower p ((k:ℤ)^2+(targetResidueLambda p n r-5)*k)
      (U*residueClassMatrix n b S r lambda Fin.val Fin.val*V).det := by
  simpa only [targetLocalWeight_floor_nonzero n r hr] using
    pairedResidueClass_integral_change_bound n b S r lambda U V hs hp hS hU hV

theorem concrete_good_class_floor_bound {p : ℕ} [Fact p.Prime]
    (n b : ℕ) (S : Finset ℤ) (r : ℤ) (lambda : Fin 4 → ℚ) {k d : ℕ}
    (U : Matrix (Fin k) (Fin d) ℚ) (V : Matrix (Fin d) (Fin k) ℚ)
    (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda) (hr : ¬(p:ℤ)∣r)
    (hS : ∀ a∈S, a∈poleWindow (100*n) ∧ ((p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) ∧ (b-a).toNat<p)
    (hU : ∀ i j, PadicLower p 0 (U i j)) (hV : ∀ i j, PadicLower p 0 (V i j)) :
    PadicLower p ((k:ℤ)^2+targetResidueLambda p n r*k)
      (U*residueClassMatrix n b S r lambda Fin.val Fin.val*V).det := by
  simpa only [targetLocalWeight_floor_nonzero n r hr] using
    pairedResidueClass_integral_change_bound_good n b S r lambda U V hs hp hS hU hV
end OddZeta.FourValue

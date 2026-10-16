import FourValueSelectedBasisValuations
import FourValueSingleNode

noncomputable section
namespace OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

theorem selectedResidueMatrix_singleNode_bound (n b : ℕ) (S : Finset ℤ) (r : ℤ)
    (lambda : Fin 4 → ℚ) {k : ℕ} (rows cols : Fin k → Fin (targetHankelDegree n+1))
    (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda)
    (hS : ∀ a∈S,a∈poleWindow (63*n) ∧ centeredResidueCount p a (63*n)=1 ∧
      ((p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) ∧ (b-a).toNat<p) :
    PadicLower p (max ((k:ℤ)^2+targetLocalWeight p n r*k)
      ((k:ℤ)*targetNormalizationFloor p n)-selectedFactorialCost p n rows cols)
      (selectedResidueMatrix n b S lambda rows cols).det := by
  apply selectedResidueMatrix_transfer n b S r lambda rows cols
  intro u v
  by_cases hu : Function.Injective u
  · by_cases hv : Function.Injective v
    · exact singleNode_residueMatrix_det_max n b S r lambda
        (fun i => (u i).val) (fun j => (v j).val)
        (Fin.val_injective.comp hu) (Fin.val_injective.comp hv) hs hp hS
    · rw [matrix_submatrix_det_zero_of_not_injective _ _ _ (Or.inr hv)]
      exact PadicLower.zero _
  · rw [matrix_submatrix_det_zero_of_not_injective _ _ _ (Or.inl hu)]
    exact PadicLower.zero _
end OddZeta.FourValue

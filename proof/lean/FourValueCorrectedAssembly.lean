import FourValueCorrectedCapacity

/-! Exact finite pole partition and all-prime local-minor assembly.
The physical-coordinate checkpoint remains unchanged; this namespace supplies
the arithmetic statements for the analytic-coordinate matrix. -/

noncomputable section
namespace OddZeta.FourValue.Corrected
open Polynomial
open scoped RatFunc
variable {p : ℕ} [Fact p.Prime]
theorem selectedResidueMatrix_allPrime_bound (n b : ℕ) (S : Finset ℤ) (lambda : Fin 4 → ℚ)
    {k : ℕ} (rows cols : Fin k → Fin (targetHankelDegree n+1))
    (hS : ∀ a∈S,a∈poleWindow (100*n) ∧ (b-a).toNat≤800*n) :
    PadicLower p ((k:ℤ)*(-40*(Nat.log p (800*n):ℤ)-
      (padicValNat p (rationalPencilDenominator lambda):ℤ)))
      (selectedResidueMatrix n b S lambda rows cols).det := by
  have h := padicLower_det_weighted (p:=p) (selectedResidueMatrix n b S lambda rows cols)
    (fun _ => 0) (fun _ => 0) _ (fun i j => by
      change PadicLower p _ (residuePolynomialFunctional n b S lambda
        (squareBasisPolynomial (rows i).val*squareBasisPolynomial (cols j).val))
      rw [residuePolynomialFunctional_apply]
      apply padicLower_sum
      intro a ha
      simpa using squareBasis_local_allPrime_bound (p:=p) n b (rows i) (cols j) a lambda (hS a ha).1 (hS a ha).2)
  simpa using h

theorem rationalFourValueMatrix_selected_partition (n : ℕ) (lambda : Fin 4 → ℚ) {k d : ℕ}
    (rows cols : Fin k → Fin (targetHankelDegree n+1)) (label : ℤ → Fin d) :
    (rationalFourValueMatrix n lambda).submatrix rows cols =
      ∑ r : Fin d,selectedResidueMatrix n (67*n)
        ((poleWindow (67*n)).filter (fun a => label a=r)) lambda rows cols := by
  rw [rationalFourValueMatrix_selected_boundary]
  ext i j
  simp only [Matrix.sum_apply,selectedResidueMatrix,polynomialGram,residuePolynomialFunctional_apply]
  exact (Finset.sum_fiberwise (poleWindow (67*n)) label
    (fun a => localFourValueObservation (67*n) a lambda
      (rationalAnalyticTest n (squareBasisPolynomial (rows i).val*squareBasisPolynomial (cols j).val)))).symm


end OddZeta.FourValue.Corrected

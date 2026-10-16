import FourValueCorrectedSmallBasis

/-! All-prime entry and minor bounds for the corrected rational matrix.
The physical-coordinate checkpoint remains unchanged; this namespace supplies
the arithmetic statements for the analytic-coordinate matrix. -/

noncomputable section
namespace OddZeta.FourValue.Corrected
open Polynomial
open scoped RatFunc
variable {p : ℕ} [Fact p.Prime]
theorem squareBasis_entry_scaledLaurent (n : ℕ) (i j : Fin (targetHankelDegree n+1))
    (a : ℤ) (ha : a∈poleWindow (100*n)) :
    ScaledLaurentPadicLower p (a:ℚ) (Nat.log p (800*n)) (-36*(Nat.log p (800*n):ℤ))
      (rationalAnalyticTest n (squareBasisPolynomial i.val*squareBasisPolynomial j.val)) := by
  have h := ((targetNormalizedWeight_scaledLaurent (p:=p) n a ha).mul
    (squareBasis_analytic_scaledLaurent (p:=p) n i a ha)).mul
    (squareBasis_analytic_scaledLaurent (p:=p) n j a ha)
  have h' := h.mono (v:=-36*(Nat.log p (800*n):ℤ)) (by have hw := targetAllPrimeWeight_lower (p:=p) n a ha; omega)
  simpa only [rationalAnalyticTest,mul_comp,map_mul,mul_assoc] using h'

theorem squareBasis_local_allPrime_bound (n b : ℕ) (i j : Fin (targetHankelDegree n+1))
    (a : ℤ) (lambda : Fin 4 → ℚ) (ha : a∈poleWindow (100*n)) (hb : (b-a).toNat≤800*n) :
    PadicLower p (-40*(Nat.log p (800*n):ℤ)-(padicValNat p (rationalPencilDenominator lambda):ℤ))
      (localFourValueObservation b a lambda
        (rationalAnalyticTest n (squareBasisPolynomial i.val*squareBasisPolynomial j.val))) := by
  let f := rationalAnalyticTest n (squareBasisPolynomial (K:=ℚ) i.val*squareBasisPolynomial j.val)
  let B : ℤ := Nat.log p (800*n)
  let Q : ℤ := padicValNat p (rationalPencilDenominator lambda)
  have hB : 0≤B := Int.natCast_nonneg _
  have hQ : 0≤Q := Int.natCast_nonneg _
  have hf (k : ℕ) : PadicLower p (-36*B+B*(k+1:ℕ))
      (rationalCoefficientAt (a:ℚ) (-((k+1:ℕ):ℤ)) f) := by
    convert squareBasis_entry_scaledLaurent (p:=p) n i j a ha (-((k+1:ℕ):ℤ)) using 1 <;> try rfl
    dsimp [B]
    ring
  have hC : PadicLower p (-40*B-Q) (localFourthObservation b a f) := by
    apply PadicLower.neg
    apply padicLower_sum
    intro k hk
    have h := ((PadicLower.natCast (p:=p) (Nat.choose (k+4) 4)).mul
      (finiteHarmonic_padicLower_log (800*n) (b-a).toNat (k+5) hb)).mul (hf k)
    apply (by simpa [mul_assoc] using h : PadicLower p _ _).mono
    dsimp [B]
    push_cast
    nlinarith
  have hl (l : Fin 4) (k : ℕ) :
      PadicLower p (-40*B-Q) (lambda l*rationalCoefficientAt (a:ℚ) (-((k+1:ℕ):ℤ)) f) := by
    apply ((rationalPencil_allPrime_lower (p:=p) lambda l).mul (hf k)).mono
    dsimp [Q]
    push_cast
    nlinarith
  exact (((hC.add (hl 0 2)).add (hl 1 4)).add (hl 2 6)).add (hl 3 8)

theorem rationalFourValueMatrix_allPrime_entry (n : ℕ) (lambda : Fin 4 → ℚ)
    (i j : Fin (targetHankelDegree n+1)) :
    PadicLower p (-40*(Nat.log p (800*n):ℤ)-(padicValNat p (rationalPencilDenominator lambda):ℤ))
      (rationalFourValueMatrix n lambda i j) := by
  change PadicLower p _ (rationalFourValueFunctional n lambda
    (squareBasisPolynomial i.val*squareBasisPolynomial j.val))
  rw [rationalFourValueFunctional_local_sum]
  apply padicLower_sum
  intro a ha
  apply squareBasis_local_allPrime_bound n (100*n) i j a lambda ha
  simp only [poleWindow,Finset.mem_Icc] at ha
  omega

theorem rationalFourValueMatrix_smallPrime_entry (n : ℕ) (lambda : Fin 4 → ℚ)
    (i j : Fin (targetHankelDegree n+1)) :
    PadicLower p (-150*(Nat.log p (800*n):ℤ)-(padicValNat p (rationalPencilDenominator lambda):ℤ))
      (rationalFourValueMatrix n lambda i j) :=
  (rationalFourValueMatrix_allPrime_entry n lambda i j).mono (by omega)

theorem rationalFourValueMatrix_allPrime_minor (n : ℕ) (lambda : Fin 4 → ℚ) {k : ℕ}
    (rows cols : Fin k → Fin (targetHankelDegree n+1)) :
    PadicLower p ((k:ℤ)*(-40*(Nat.log p (800*n):ℤ)-
      (padicValNat p (rationalPencilDenominator lambda):ℤ)))
      ((rationalFourValueMatrix n lambda).submatrix rows cols).det := by
  have h := padicLower_det_weighted (p:=p) ((rationalFourValueMatrix n lambda).submatrix rows cols)
    (fun _ => 0) (fun _ => 0) _ (fun i j => by
      simpa using rationalFourValueMatrix_allPrime_entry (p:=p) n lambda (rows i) (cols j))
  simpa using h


end OddZeta.FourValue.Corrected

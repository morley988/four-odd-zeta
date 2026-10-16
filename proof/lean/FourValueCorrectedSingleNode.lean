import FourValueCorrectedSmallEntries

/-! Single-node improvement in the corrected coordinates.
The physical-coordinate checkpoint remains unchanged; this namespace supplies
the arithmetic statements for the analytic-coordinate matrix. -/

noncomputable section
namespace OddZeta.FourValue.Corrected
open Polynomial
open scoped RatFunc
variable {p : ℕ} [Fact p.Prime]
theorem analyticSubstitution_polynomialPadicLower {w : ℤ} {P : ℚ[X]}
    (hP : PolynomialPadicLower p w P) : PolynomialPadicLower p w (P.comp (X^2)) := by
  have hx : PolynomialPadicLower p 0 (X : ℚ[X]) := by
    simpa using integerLinearFactor_polynomialPadicLower (p:=p) 0
  exact hP.comp_integral (by simpa using hx.pow 2)

theorem rationalAnalyticTest_uniformLaurent (n : ℕ) (a : ℤ) (P : ℚ[X]) (w : ℤ)
    (hP : PolynomialPadicLower p w P)
    (ha : ∀ t∈targetPoleList n,a=t ∨ ¬(p:ℤ)∣a-t) :
    UniformLaurentPadicLower p (a:ℚ) (targetNormalizationValuation p n+w)
      (rationalAnalyticTest n P) := by
  have hx : PolynomialPadicLower p 0 (X : ℚ[X]) := by
    simpa using integerLinearFactor_polynomialPadicLower (p:=p) 0
  have hn : PolynomialPadicLower p 0 (C 2*X*(targetGapPolynomial (K:=ℚ) n)^5) := by
    simpa using ((PolynomialPadicLower.constant (PadicLower.natCast (p:=p) 2)).mul hx).mul
      ((targetGapPolynomial_integral (p:=p) n).pow 5)
  have hc : PadicLower p (targetNormalizationValuation p n) (targetNormalization (K:=ℚ) n) :=
    Or.inr (by rw [targetNormalization_padicVal])
  have hd := inverseIntegerRootProduct_uniformLaurent a (targetPoleList n) ha
  rw [← targetReducedDenominator_list] at hd
  have h := ((UniformLaurentPadicLower.constant (a:=(a:ℚ)) hc).mul
    ((UniformLaurentPadicLower.polynomial hn a).mul hd)).mul
    (UniformLaurentPadicLower.polynomial (analyticSubstitution_polynomialPadicLower hP) a)
  simpa [rationalAnalyticTest,targetNormalizedWeight_cancelled,div_eq_mul_inv] using h
theorem singleNode_local_good (n b : ℕ) (a : ℤ) (lambda : Fin 4 → ℚ)
    (P : ℚ[X]) (w : ℤ) (hP : PolynomialPadicLower p w P)
    (ha : a∈poleWindow (63*n)) (hc : centeredResidueCount p a (63*n)=1)
    (hm : (b-a).toNat<p) (hp : ¬p∣rationalPencilDenominator lambda) :
    PadicLower p (targetNormalizationValuation p n+w)
      (localFourValueObservation b a lambda (rationalAnalyticTest n P)) := by
  apply localFourValueObservation_uniform_good _ _ _ _ _ hm
    (rationalPencil_integral_at_prime lambda hp)
  intro k hk
  exact rationalAnalyticTest_uniformLaurent n a P w hP
    (singleNode_root_condition n a ha hc) _

theorem translatedAnalyticMonomial_integral (r : ℤ) (m : ℕ) :
    PolynomialPadicLower p 0 (translatedAnalyticMonomial r m) := by
  have h := (integerLinearFactor_polynomialPadicLower (p:=p) (r^2)).pow m
  simpa [translatedAnalyticMonomial] using h

theorem singleNode_residueMatrix_det (n b : ℕ) (S : Finset ℤ) (r : ℤ)
    (lambda : Fin 4 → ℚ) {k : ℕ} (rows cols : Fin k → ℕ)
    (hp : ¬p∣rationalPencilDenominator lambda)
    (hS : ∀ a∈S,a∈poleWindow (63*n) ∧ centeredResidueCount p a (63*n)=1 ∧ (b-a).toNat<p) :
    PadicLower p ((k:ℤ)*targetNormalizationValuation p n)
      (residueClassMatrix n b S r lambda rows cols).det := by
  have h := padicLower_det_weighted (p:=p) (residueClassMatrix n b S r lambda rows cols)
    (fun _ => 0) (fun _ => 0) (targetNormalizationValuation p n) (fun i j => by
      apply padicLower_sum
      intro a ha
      obtain ⟨haw,hac,hab⟩ := hS a ha
      simpa using singleNode_local_good n b a lambda _ 0
        (translatedAnalyticMonomial_integral r (rows i+cols j)) haw hac hab hp)
  simpa using h

theorem singleNode_residueMatrix_det_max (n b : ℕ) (S : Finset ℤ) (r : ℤ)
    (lambda : Fin 4 → ℚ) {k : ℕ} (rows cols : Fin k → ℕ)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda)
    (hS : ∀ a∈S,a∈poleWindow (63*n) ∧ centeredResidueCount p a (63*n)=1 ∧
      ((p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) ∧ (b-a).toNat<p) :
    PadicLower p (max ((k:ℤ)^2+targetLocalWeight p n r*k)
      ((k:ℤ)*targetNormalizationFloor p n))
      (residueClassMatrix n b S r lambda rows cols).det := by
  apply PadicLower.max
  · apply pairedResidueClassMatrix_det_padicLower_good n b S r lambda rows cols hr hc hs hp
    intro a ha
    obtain ⟨haw,hac,har,hab⟩ := hS a ha
    refine ⟨?_,har,hab⟩
    simp only [poleWindow,Finset.mem_Icc] at haw ⊢
    omega
  · have h := singleNode_residueMatrix_det n b S r lambda rows cols hp
      (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1,(hS a ha).2.2.2⟩)
    rw [← targetNormalization_padicVal, targetNormalization_padicVal_large n hs] at h
    exact h

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

end OddZeta.FourValue.Corrected

import FourValueAnalyticCoordinates

/-! Corrected x²-coordinate rational tests and paired residue-class valuation bounds.
The physical-coordinate checkpoint remains unchanged; this namespace supplies
the arithmetic statements for the analytic-coordinate matrix. -/

noncomputable section
namespace OddZeta.FourValue.Corrected
open Polynomial
open scoped RatFunc
variable {p : ℕ} [Fact p.Prime]
def rationalAnalyticTest (n : ℕ) (P : ℚ[X]) : RatFunc ℚ :=
  targetNormalizedWeight n * algebraMap ℚ[X] (RatFunc ℚ) (P.comp (X^2))

theorem rationalAnalyticTest_eq (n : ℕ) (P : ℚ[X]) :
    rationalAnalyticTest n P = rationalPhysicalTest n (analyticCoordinate P) := by
  rw [rationalPhysicalTest,analyticCoordinate_cancel]
  rfl

def rationalFourValueFunctional (n : ℕ) (lambda : Fin 4 → ℚ) : ℚ[X] →ₗ[ℚ] ℚ :=
  analyticFunctional (OddZeta.FourValue.rationalFourValueFunctional n lambda)

def rationalFourValueMatrix (n : ℕ) (lambda : Fin 4 → ℚ) :=
  squareBasisGram (rationalFourValueFunctional n lambda) (targetHankelDegree n)

theorem rationalFourValueFunctional_local_sum (n : ℕ) (lambda : Fin 4 → ℚ) (P : ℚ[X]) :
    rationalFourValueFunctional n lambda P =
      ∑ a ∈ poleWindow (100*n), localFourValueObservation (100*n) a lambda (rationalAnalyticTest n P) := by
  change OddZeta.FourValue.rationalFourValueFunctional n lambda (analyticCoordinate P) = _
  rw [OddZeta.FourValue.rationalFourValueFunctional_local_sum]
  simp only [rationalAnalyticTest_eq]

theorem rationalFourValueFunctional_local_sum_67 (n : ℕ) (lambda : Fin 4 → ℚ) (P : ℚ[X])
    (hP : P.natDegree≤361*n+3) :
    rationalFourValueFunctional n lambda P =
      ∑ a ∈ poleWindow (67*n), localFourValueObservation (67*n) a lambda (rationalAnalyticTest n P) := by
  change OddZeta.FourValue.rationalFourValueFunctional n lambda (analyticCoordinate P) = _
  rw [OddZeta.FourValue.rationalFourValueFunctional_local_sum_67 n lambda _
    (by simpa [analyticCoordinate_natDegree] using hP)]
  simp only [rationalAnalyticTest_eq]

def translatedAnalyticMonomial (r : ℤ) (m : ℕ) : ℚ[X] := (X-C ((r:ℚ)^2))^m

theorem translatedAnalyticMonomial_laurentPadicLower (a r : ℤ) (m : ℕ)
    (har : (p:ℤ) ∣ a-r) :
    LaurentPadicLower p (a:ℚ) (m:ℤ)
      (algebraMap ℚ[X] (RatFunc ℚ) ((translatedAnalyticMonomial r m).comp (X^2))) := by
  have h1 := linearFactor_laurentPadicLower (p:=p) a r
  have h2 := linearFactor_laurentPadicLower (p:=p) a (-r)
  have hr : rootResidueWeight p (a-r)=1 := by
    simp [rootResidueWeight, Int.natCast_dvd.mp har]
  rw [hr] at h1
  have h := (h1.mul h2).mono (show (1:ℤ) ≤ 1+rootResidueWeight p (a- -r) by
    have := (rootResidueWeight_bounds (p:=p) (a- -r)).1
    omega)
  have he : (translatedAnalyticMonomial r m).comp (X^2) =
      ((X-C (r:ℚ))*(X-C ((-r:ℤ):ℚ)))^m := by
    simp only [translatedAnalyticMonomial,pow_comp,sub_comp,X_comp,C_comp,Int.cast_neg]
    congr 1
    simp only [map_pow,map_neg]
    ring
  rw [he,map_pow,map_mul]
  simpa using h.pow m

theorem rationalAnalyticTest_translated_padicLower (n : ℕ) (a r : ℤ) (m : ℕ)
    (ha : a∈poleWindow (100*n)) (hs : 800*n<p^2) (har : (p:ℤ)∣a-r) (k : ℕ) :
    PadicLower p (targetLocalWeight p n r + m + k)
      (rationalCoefficientAt (a:ℚ) (-(k:ℤ))
        (rationalAnalyticTest n (translatedAnalyticMonomial r m))) := by
  have h := (targetNormalizedWeight_laurentPadicLower n a ha hs).mul
    (translatedAnalyticMonomial_laurentPadicLower a r m har)
  have hc := h (-(k:ℤ))
  rw [targetLocalWeight_congr n a r har] at hc
  simpa [rationalAnalyticTest] using hc
def residueClassMatrix (n b : ℕ) (S : Finset ℤ) (r : ℤ) (lambda : Fin 4 → ℚ)
    {k : ℕ} (rows cols : Fin k → ℕ) : Matrix (Fin k) (Fin k) ℚ :=
  fun i j => ∑ a ∈ S, localFourValueObservation b a lambda
    (rationalAnalyticTest n (translatedAnalyticMonomial r (rows i+cols j)))
theorem rationalAnalyticTest_translated_padicLower_paired (n : ℕ) (a r : ℤ) (m : ℕ)
    (ha : a∈poleWindow (100*n)) (hs : 800*n<p^2)
    (har : (p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) (k : ℕ) :
    PadicLower p (targetLocalWeight p n r + m + k)
      (rationalCoefficientAt (a:ℚ) (-(k:ℤ))
        (rationalAnalyticTest n (translatedAnalyticMonomial r m))) := by
  rcases har with har | har
  · exact rationalAnalyticTest_translated_padicLower n a r m ha hs har k
  · have h := rationalAnalyticTest_translated_padicLower n a (-r) m ha hs
      (by simpa using har) k
    simpa [targetLocalWeight_neg, translatedAnalyticMonomial] using h
theorem pairedResidueClassMatrix_det_padicLower (n b : ℕ) (S : Finset ℤ) (r : ℤ)
    (lambda : Fin 4 → ℚ) {k : ℕ} (rows cols : Fin k → ℕ)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda)
    (hS : ∀ a∈S, a∈poleWindow (100*n) ∧ ((p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) ∧ (b-a).toNat<p^2) :
    PadicLower p ((k:ℤ)^2+(targetLocalWeight p n r-5)*k)
      (residueClassMatrix n b S r lambda rows cols).det := by
  apply padicLower_det_bad_cell _ rows cols hr hc
  intro i j
  apply padicLower_sum
  intro a ha
  obtain ⟨haw, har, hab⟩ := hS a ha
  have h := localFourValueObservation_padicLower b a lambda _
    (targetLocalWeight p n r+(rows i+cols j:ℕ)) hab
    (rationalPencil_integral_at_prime lambda hp)
    (fun l hlt => rationalAnalyticTest_translated_padicLower_paired n a r _ haw hs har (l+1))
  convert h using 1 <;> try rfl
  push_cast
  ring
theorem pairedResidueClassMatrix_det_padicLower_good (n b : ℕ) (S : Finset ℤ) (r : ℤ)
    (lambda : Fin 4 → ℚ) {k : ℕ} (rows cols : Fin k → ℕ)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda)
    (hS : ∀ a∈S, a∈poleWindow (100*n) ∧ ((p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) ∧ (b-a).toNat<p) :
    PadicLower p ((k:ℤ)^2+targetLocalWeight p n r*k)
      (residueClassMatrix n b S r lambda rows cols).det := by
  suffices hh : ∀ i j, PadicLower p ((rows i:ℤ)+cols j+(targetLocalWeight p n r+1))
      (residueClassMatrix n b S r lambda rows cols i j) by
    simpa using padicLower_det_distinct_indices _ rows cols hr hc (targetLocalWeight p n r+1) hh
  intro i j
  apply padicLower_sum
  intro a ha
  obtain ⟨haw, har, hab⟩ := hS a ha
  have h := localFourValueObservation_padicLower_good b a lambda _
    (targetLocalWeight p n r+(rows i+cols j:ℕ)) hab
    (rationalPencil_integral_at_prime lambda hp)
    (fun l hlt => rationalAnalyticTest_translated_padicLower_paired n a r _ haw hs har (l+1))
  convert h using 1 <;> try rfl
  push_cast
  ring

end OddZeta.FourValue.Corrected

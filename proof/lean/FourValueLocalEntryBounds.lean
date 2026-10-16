import FourValueTargetValuations
import FourValueIndexBounds

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {p : ℕ} [Fact p.Prime]

def rationalPhysicalTest (n : ℕ) (P : ℚ[X]) : RatFunc ℚ :=
  targetNormalizedWeight n * algebraMap ℚ[X] (RatFunc ℚ) ((P.comp (C 4*X)).comp (X^2))

theorem rationalPhysicalFunctional_test (n : ℕ) (i : Fin 9) (P : ℚ[X]) :
    rationalPhysicalFunctional n i P = nineRationalObservations (100*n) i
      (rationalPhysicalTest n P) := by
  simp [rationalPhysicalFunctional, normalizedTargetFunctional, normalizedTupleTest,
    rationalPhysicalTest, targetNormalizedWeight, tupleRationalTest,
    RatFunc.smul_eq_C_mul, mul_assoc]

theorem rootResidueWeight_congr (a r t : ℤ) (h : (p:ℤ) ∣ a-r) :
    rootResidueWeight p (a-t) = rootResidueWeight p (r-t) := by
  unfold rootResidueWeight
  congr 1
  rw [← Int.natCast_dvd, ← Int.natCast_dvd]
  have he : a-t = (a-r)+(r-t) := by ring
  rw [he, dvd_add_right h]

theorem centeredResidueCount_congr (a r : ℤ) (b : ℕ) (h : (p:ℤ) ∣ a-r) :
    centeredResidueCount p a b = centeredResidueCount p r b := by
  apply Finset.sum_congr rfl
  intro t ht
  exact rootResidueWeight_congr a r t h

theorem targetLocalWeight_congr (n : ℕ) (a r : ℤ) (h : (p:ℤ) ∣ a-r) :
    targetLocalWeight p n a = targetLocalWeight p n r := by
  have hz := rootResidueWeight_congr a r 0 h
  simp only [sub_zero] at hz
  simp [targetLocalWeight, hz, centeredResidueCount_congr a r _ h]

def translatedPhysicalMonomial (r : ℤ) (m : ℕ) : ℚ[X] := (X-C (4*(r:ℚ)^2))^m

/-- Each translated square-variable power gains m powers of p. This
statement explicitly incorporates the checked coordinate X=4x². -/
theorem translatedPhysicalMonomial_laurentPadicLower (a r : ℤ) (m : ℕ)
    (har : (p:ℤ) ∣ a-r) :
    LaurentPadicLower p (a:ℚ) (m:ℤ)
      (algebraMap ℚ[X] (RatFunc ℚ)
        (((translatedPhysicalMonomial r m).comp (C 4*X)).comp (X^2))) := by
  have h1 := linearFactor_laurentPadicLower (p:=p) a r
  have h2 := linearFactor_laurentPadicLower (p:=p) a (-r)
  have hr : rootResidueWeight p (a-r)=1 := by
    simp [rootResidueWeight, Int.natCast_dvd.mp har]
  rw [hr] at h1
  have h := ((LaurentPadicLower.constant (a:=(a:ℚ)) (PadicLower.natCast (p:=p) 4)).mul
    (h1.mul h2)).mono (show (1:ℤ) ≤ 0+(1+rootResidueWeight p (a- -r)) by
      have := (rootResidueWeight_bounds (p:=p) (a- -r)).1
      omega)
  have he : ((translatedPhysicalMonomial r m).comp (C 4*X)).comp (X^2) =
      (C (4:ℚ)*((X-C (r:ℚ))*(X-C ((-r:ℤ):ℚ))))^m := by
    simp only [translatedPhysicalMonomial, Polynomial.pow_comp, Polynomial.sub_comp,
      Polynomial.X_comp, Polynomial.C_comp, Polynomial.mul_comp, Int.cast_neg]
    congr 1
    simp only [map_mul, map_pow, map_neg]
    ring
  rw [he, map_pow, map_mul, map_mul]
  simpa using h.pow m

theorem rationalPhysicalTest_translated_padicLower (n : ℕ) (a r : ℤ) (m : ℕ)
    (ha : a∈poleWindow (100*n)) (hs : 800*n<p^2) (har : (p:ℤ)∣a-r) (k : ℕ) :
    PadicLower p (targetLocalWeight p n r + m + k)
      (rationalCoefficientAt (a:ℚ) (-(k:ℤ))
        (rationalPhysicalTest n (translatedPhysicalMonomial r m))) := by
  have h := (targetNormalizedWeight_laurentPadicLower n a ha hs).mul
    (translatedPhysicalMonomial_laurentPadicLower a r m har)
  have hc := h (-(k:ℤ))
  rw [targetLocalWeight_congr n a r har] at hc
  simpa [rationalPhysicalTest] using hc

/-- One pole's exact contribution to the fourth harmonic observation.
The boundary b is explicit so both the 100n and 67n conventions can be used. -/
def localFourthObservation (b : ℕ) (a : ℤ) (f : RatFunc ℚ) : ℚ :=
  -∑ k ∈ Finset.range 10, (Nat.choose (k+4) 4:ℚ)*finiteHarmonic ((b-a).toNat) (k+5)*
      rationalCoefficientAt (a:ℚ) (-((k+1:ℕ):ℤ)) f

theorem localFourthObservation_padicLower (b : ℕ) (a : ℤ) (f : RatFunc ℚ) (w : ℤ)
    (hm : (b-a).toNat<p^2)
    (hf : ∀ k<10, PadicLower p (w+(k+1:ℕ))
      (rationalCoefficientAt (a:ℚ) (-((k+1:ℕ):ℤ)) f)) :
    PadicLower p (w-4) (localFourthObservation b a f) := by
  apply PadicLower.neg
  apply padicLower_sum
  intro k hk
  have h := (fourthHarmonicBracket_padicLower (b-a).toNat k hm).mul
    (hf k (Finset.mem_range.mp hk))
  convert h using 1 <;> try rfl
  push_cast
  ring

theorem localFourthObservation_padicLower_good (b : ℕ) (a : ℤ) (f : RatFunc ℚ) (w : ℤ)
    (hm : (b-a).toNat<p)
    (hf : ∀ k<10, PadicLower p (w+(k+1:ℕ))
      (rationalCoefficientAt (a:ℚ) (-((k+1:ℕ):ℤ)) f)) :
    PadicLower p (w+1) (localFourthObservation b a f) := by
  apply PadicLower.neg
  apply padicLower_sum
  intro k hk
  have h := (fourthHarmonicBracket_padicLower_good (b-a).toNat k hm).mul
    (hf k (Finset.mem_range.mp hk))
  exact h.mono (by push_cast; omega)

/-- Concrete bad-class local entry bound; no Laurent bound is assumed. -/
theorem target_localFourth_translated_bound (n b : ℕ) (a r : ℤ) (m : ℕ)
    (ha : a∈poleWindow (100*n)) (hs : 800*n<p^2) (har : (p:ℤ)∣a-r)
    (hb : (b-a).toNat<p^2) :
    PadicLower p (targetLocalWeight p n r + m - 4)
      (localFourthObservation b a (rationalPhysicalTest n (translatedPhysicalMonomial r m))) := by
  exact localFourthObservation_padicLower b a _ _ hb
    (fun k hk => rationalPhysicalTest_translated_padicLower n a r m ha hs har (k+1))

/-- Concrete good-class gain of five over the preceding bound. -/
theorem target_localFourth_translated_bound_good (n b : ℕ) (a r : ℤ) (m : ℕ)
    (ha : a∈poleWindow (100*n)) (hs : 800*n<p^2) (har : (p:ℤ)∣a-r)
    (hb : (b-a).toNat<p) :
    PadicLower p (targetLocalWeight p n r + m + 1)
      (localFourthObservation b a (rationalPhysicalTest n (translatedPhysicalMonomial r m))) := by
  exact localFourthObservation_padicLower_good b a _ _ hb
    (fun k hk => rationalPhysicalTest_translated_padicLower n a r m ha hs har (k+1))
end OddZeta.FourValue

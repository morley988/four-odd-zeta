import FourValueLocalEntryBounds

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {p : ℕ} [Fact p.Prime]

def localFourValueObservation (b : ℕ) (a : ℤ) (lambda : Fin 4 → ℚ) (f : RatFunc ℚ) : ℚ :=
  localFourthObservation b a f +
    lambda 0*rationalCoefficientAt (a:ℚ) (-3) f +
    lambda 1*rationalCoefficientAt (a:ℚ) (-5) f +
    lambda 2*rationalCoefficientAt (a:ℚ) (-7) f +
    lambda 3*rationalCoefficientAt (a:ℚ) (-9) f

/-- Exact decomposition of the rational model into its concrete pole terms. -/
theorem rationalFourValueFunctional_local_sum (n : ℕ) (lambda : Fin 4 → ℚ) (P : ℚ[X]) :
    rationalFourValueFunctional n lambda P =
      ∑ a ∈ poleWindow (100*n), localFourValueObservation (100*n) a lambda (rationalPhysicalTest n P) := by
  simp only [rationalFourValueFunctional, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, rationalPhysicalFunctional_test]
  simp [nineRationalObservations, rationalB, rationalC, localFourValueObservation,
    localFourthObservation, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_neg_distrib,
    smul_eq_mul, mul_assoc]
  norm_num [show ∀ i : ℕ, i+4+1=i+5 by omega]

theorem localFourValueObservation_padicLower (b : ℕ) (a : ℤ) (lambda : Fin 4 → ℚ)
    (f : RatFunc ℚ) (w : ℤ) (hm : (b-a).toNat<p^2)
    (hl : ∀ i, PadicLower p 0 (lambda i))
    (hf : ∀ k<10, PadicLower p (w+(k+1:ℕ))
      (rationalCoefficientAt (a:ℚ) (-((k+1:ℕ):ℤ)) f)) :
    PadicLower p (w-4) (localFourValueObservation b a lambda f) := by
  have h (i : Fin 4) (k : ℕ) (hk : k<10) :
      PadicLower p (w-4) (lambda i*rationalCoefficientAt (a:ℚ) (-((k+1:ℕ):ℤ)) f) :=
    ((hl i).mul (hf k hk)).mono (by push_cast; omega)
  exact ((((localFourthObservation_padicLower b a f w hm hf).add
    (h 0 2 (by decide))).add (h 1 4 (by decide))).add (h 2 6 (by decide))).add
      (h 3 8 (by decide))

theorem localFourValueObservation_padicLower_good (b : ℕ) (a : ℤ) (lambda : Fin 4 → ℚ)
    (f : RatFunc ℚ) (w : ℤ) (hm : (b-a).toNat<p)
    (hl : ∀ i, PadicLower p 0 (lambda i))
    (hf : ∀ k<10, PadicLower p (w+(k+1:ℕ))
      (rationalCoefficientAt (a:ℚ) (-((k+1:ℕ):ℤ)) f)) :
    PadicLower p (w+1) (localFourValueObservation b a lambda f) := by
  have h (i : Fin 4) (k : ℕ) (hk : k<10) :
      PadicLower p (w+1) (lambda i*rationalCoefficientAt (a:ℚ) (-((k+1:ℕ):ℤ)) f) :=
    ((hl i).mul (hf k hk)).mono (by push_cast; omega)
  exact ((((localFourthObservation_padicLower_good b a f w hm hf).add
    (h 0 2 (by decide))).add (h 1 4 (by decide))).add (h 2 6 (by decide))).add
      (h 3 8 (by decide))

/-- Local matrix for any finite selection of poles in one residue class. -/
def residueClassMatrix (n b : ℕ) (S : Finset ℤ) (r : ℤ) (lambda : Fin 4 → ℚ)
    {k : ℕ} (rows cols : Fin k → ℕ) : Matrix (Fin k) (Fin k) ℚ :=
  fun i j => ∑ a ∈ S, localFourValueObservation b a lambda
    (rationalPhysicalTest n (translatedPhysicalMonomial r (rows i+cols j)))

/-- The bad-class quadratic bound now applies to an explicitly defined
matrix of the actual rational family, rather than assumed entry estimates. -/
theorem residueClassMatrix_det_padicLower (n b : ℕ) (S : Finset ℤ) (r : ℤ)
    (lambda : Fin 4 → ℚ) {k : ℕ} (rows cols : Fin k → ℕ)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hs : 800*n<p^2) (hl : ∀ i, PadicLower p 0 (lambda i))
    (hS : ∀ a∈S, a∈poleWindow (100*n) ∧ (p:ℤ)∣a-r ∧ (b-a).toNat<p^2) :
    PadicLower p ((k:ℤ)^2+(targetLocalWeight p n r-5)*k)
      (residueClassMatrix n b S r lambda rows cols).det := by
  apply padicLower_det_bad_cell _ rows cols hr hc
  intro i j
  apply padicLower_sum
  intro a ha
  obtain ⟨haw, har, hab⟩ := hS a ha
  have h := localFourValueObservation_padicLower b a lambda _
    (targetLocalWeight p n r+(rows i+cols j:ℕ)) hab hl
    (fun l hlt => rationalPhysicalTest_translated_padicLower n a r _ haw hs har (l+1))
  convert h using 1 <;> try rfl
  push_cast
  ring

theorem residueClassMatrix_det_padicLower_good (n b : ℕ) (S : Finset ℤ) (r : ℤ)
    (lambda : Fin 4 → ℚ) {k : ℕ} (rows cols : Fin k → ℕ)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hs : 800*n<p^2) (hl : ∀ i, PadicLower p 0 (lambda i))
    (hS : ∀ a∈S, a∈poleWindow (100*n) ∧ (p:ℤ)∣a-r ∧ (b-a).toNat<p) :
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
    (targetLocalWeight p n r+(rows i+cols j:ℕ)) hab hl
    (fun l hlt => rationalPhysicalTest_translated_padicLower n a r _ haw hs har (l+1))
  convert h using 1 <;> try rfl
  push_cast
  ring
end OddZeta.FourValue

import FourValueArithmeticDenominators

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem centeredResidueCount_eq_card (a : ℤ) (b : ℕ) :
    centeredResidueCount p a b =
      (((poleWindow b).filter (fun t => (p:ℤ)∣a-t)).card:ℤ) := by
  simp [centeredResidueCount, rootResidueWeight, ← Int.natCast_dvd, Finset.sum_boole]

theorem centeredResidueCount_nonneg (a : ℤ) (b : ℕ) : 0≤centeredResidueCount p a b := by
  rw [centeredResidueCount_eq_card]
  exact Int.natCast_nonneg _

theorem centeredResidueCount_neg (a : ℤ) (b : ℕ) :
    centeredResidueCount p (-a) b = centeredResidueCount p a b := by
  unfold centeredResidueCount
  apply Finset.sum_bij (fun t ht => -t)
  · intro t ht
    simp only [poleWindow, Finset.mem_Icc] at ht ⊢
    omega
  · intro t ht u hu he
    exact neg_injective he
  · intro t ht
    refine ⟨-t, ?_, by simp⟩
    simp only [poleWindow, Finset.mem_Icc] at ht ⊢
    omega
  · intro t ht
    have he : -a-t = -(a- -t) := by ring
    rw [he]
    simp only [rootResidueWeight, Int.natAbs_neg]

theorem targetLocalWeight_neg (n : ℕ) (a : ℤ) :
    targetLocalWeight p n (-a) = targetLocalWeight p n a := by
  simp [targetLocalWeight, centeredResidueCount_neg, rootResidueWeight]

/-- Paired x-residue classes give the same bound for the square coordinate. -/
theorem rationalPhysicalTest_translated_padicLower_paired (n : ℕ) (a r : ℤ) (m : ℕ)
    (ha : a∈poleWindow (100*n)) (hs : 800*n<p^2)
    (har : (p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) (k : ℕ) :
    PadicLower p (targetLocalWeight p n r + m + k)
      (rationalCoefficientAt (a:ℚ) (-(k:ℤ))
        (rationalPhysicalTest n (translatedPhysicalMonomial r m))) := by
  rcases har with har | har
  · exact rationalPhysicalTest_translated_padicLower n a r m ha hs har k
  · have h := rationalPhysicalTest_translated_padicLower n a (-r) m ha hs
      (by simpa using har) k
    simpa [targetLocalWeight_neg, translatedPhysicalMonomial] using h

/-- The precise coefficient cost also holds for a full paired residue class. -/
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
    (fun l hlt => rationalPhysicalTest_translated_padicLower_paired n a r _ haw hs har (l+1))
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
    (fun l hlt => rationalPhysicalTest_translated_padicLower_paired n a r _ haw hs har (l+1))
  convert h using 1 <;> try rfl
  push_cast
  ring
end OddZeta.FourValue

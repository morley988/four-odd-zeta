import FourValueRationalCoefficients
import FourValuePadicMinors
import ReusedCoefficients

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem padicValRat_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, padicValRat.mul
      (hf a (by simp)) (Finset.prod_ne_zero_iff.mpr (fun i hi => hf i (by simp [hi]))),
      ih (fun i hi => hf i (by simp [hi]))]

def targetNormalizationValuation (p n : ℕ) : ℤ :=
  (∑ i : Fin 10, (padicValNat p (2*targetFactorialEndpoints i*n).factorial : ℤ)) -
    10*padicValNat p (33*n).factorial

def targetNormalizationFloor (p n : ℕ) : ℤ :=
  (∑ i : Fin 10, ((2*targetFactorialEndpoints i*n/p : ℕ) : ℤ)) -
    10*((33*n/p : ℕ) : ℤ)

theorem targetNormalization_padicVal (n : ℕ) :
    padicValRat p (targetNormalization (K:=ℚ) n) = targetNormalizationValuation p n := by
  rw [targetNormalization, padicValRat.div]
  · simp [padicValRat_finset_prod, Nat.factorial_ne_zero, targetNormalizationValuation]
  · exact Finset.prod_ne_zero_iff.mpr (fun i hi => by exact_mod_cast Nat.factorial_ne_zero _)
  · exact pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero (33*n))

theorem targetFactorialEndpoints_le (i : Fin 10) : targetFactorialEndpoints i ≤ 63 := by
  fin_cases i <;> norm_num [targetFactorialEndpoints]

/-- Exact formula (42), with the large-prime threshold discharged. -/
theorem targetNormalization_padicVal_large (n : ℕ) (hn : 800*n < p^2) :
    padicValRat p (targetNormalization (K:=ℚ) n) = targetNormalizationFloor p n := by
  rw [targetNormalization_padicVal]
  unfold targetNormalizationValuation targetNormalizationFloor
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [OddZeta.Coefficients.factorial_valuation_below_square p _ (by
      have h := targetFactorialEndpoints_le i
      nlinarith)]
  · rw [OddZeta.Coefficients.factorial_valuation_below_square p _ (by omega)]

theorem PadicLower.intCast (z : ℤ) : PadicLower p 0 (z:ℚ) := by
  right
  simp only [padicValRat.of_int]
  exact Int.natCast_nonneg _

theorem PadicLower.natCast (n : ℕ) : PadicLower p 0 (n:ℚ) := by
  right
  simp

theorem PadicLower.pow {a : ℤ} {q : ℚ} (hq : PadicLower p a q) (k : ℕ) :
    PadicLower p ((k:ℤ)*a) (q^k) := by
  induction k with
  | zero => simp [PadicLower]
  | succ k ih =>
    convert ih.mul hq using 1 <;> simp [pow_succ, add_mul]

/-- Multiplication by an integer cannot worsen a lower bound. -/
theorem PadicLower.int_mul {a : ℤ} {q : ℚ} (hq : PadicLower p a q) (z : ℤ) :
    PadicLower p a ((z:ℚ)*q) := by
  simpa using (PadicLower.intCast (p:=p) z).mul hq

theorem padicValNat_lt_square_le_one (m : ℕ) (hm : 0<m) (hs : m<p^2) :
    padicValNat p m ≤ 1 := by
  by_contra h
  have hd := pow_padicValNat_dvd (p:=p) (n:=m)
  have hd' : p^2 ∣ m := (pow_dvd_pow p (by omega : 2 ≤ padicValNat p m)).trans hd
  exact (not_le_of_gt hs) (Nat.le_of_dvd hm hd')

theorem harmonicTerm_padicLower (m s : ℕ) (hm : 0<m) (hs : m<p^2) :
    PadicLower p (-(s:ℤ)) (1/(m:ℚ)^s) := by
  right
  simp only [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat]
  have h := padicValNat_lt_square_le_one (p:=p) m hm hs
  have hc : (padicValNat p m:ℤ) ≤ 1 := by exact_mod_cast h
  nlinarith

theorem finiteHarmonic_padicLower (m s : ℕ) (hm : m<p^2) :
    PadicLower p (-(s:ℤ)) (finiteHarmonic (K:=ℚ) m s) := by
  apply padicLower_sum
  intro r hr
  exact harmonicTerm_padicLower (r+1) s (by omega)
    (lt_of_le_of_lt (by simpa using Finset.mem_range.mp hr) hm)

theorem finiteHarmonic_padicLower_good (m s : ℕ) (hm : m<p) :
    PadicLower p 0 (finiteHarmonic (K:=ℚ) m s) := by
  apply padicLower_sum
  intro r hr
  right
  have hr' : r+1<p := lt_of_le_of_lt (by simpa using Finset.mem_range.mp hr) hm
  have hv : padicValNat p (r+1)=0 := padicValNat.eq_zero_of_not_dvd
    (fun h => (not_le_of_gt hr') (Nat.le_of_dvd (by omega) h))
  simp only [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat, hv]
  simp

/-- The exact harmonic bracket loses at most k+5 powers at order -(k+1). -/
theorem fourthHarmonicBracket_padicLower (m k : ℕ) (hm : m<p^2) :
    PadicLower p (-((k+5:ℕ):ℤ))
      ((Nat.choose (k+4) 4:ℚ)*finiteHarmonic (K:=ℚ) m (k+5)) := by
  simpa using (PadicLower.natCast (p:=p) (Nat.choose (k+4) 4)).mul
    (finiteHarmonic_padicLower m (k+5) hm)

theorem fourthHarmonicBracket_padicLower_good (m k : ℕ) (hm : m<p) :
    PadicLower p 0
      ((Nat.choose (k+4) 4:ℚ)*finiteHarmonic (K:=ℚ) m (k+5)) := by
  simpa using (PadicLower.natCast (p:=p) (Nat.choose (k+4) 4)).mul
    (finiteHarmonic_padicLower_good m (k+5) hm)
end OddZeta.FourValue

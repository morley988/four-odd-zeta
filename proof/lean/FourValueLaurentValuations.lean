import FourValueConcreteValuations

noncomputable section
namespace OddZeta.FourValue
open Polynomial
open scoped LaurentSeries RatFunc
variable {p : ℕ} [Fact p.Prime]

/-- A bound on every Laurent coefficient, in the original x coordinate. -/
def LaurentPadicLower (p : ℕ) (a : ℚ) (w : ℤ) (f : RatFunc ℚ) : Prop :=
  ∀ j : ℤ, PadicLower p (w-j) (rationalCoefficientAt a j f)

theorem LaurentPadicLower.mul {a : ℚ} {w v : ℤ} {f g : RatFunc ℚ}
    (hf : LaurentPadicLower p a w f) (hg : LaurentPadicLower p a v g) :
    LaurentPadicLower p a (w+v) (f*g) := by
  intro j
  change PadicLower p (w+v-j) ((rationalLaurentAt a (f*g)).coeff j)
  rw [map_mul, HahnSeries.coeff_mul]
  apply padicLower_sum
  intro ij hij
  have he : ij.1+ij.2=j := (Finset.mem_antidiagonal.mp hij).2.2
  convert (hf ij.1).mul (hg ij.2) using 1 <;> try rfl
  omega

theorem LaurentPadicLower.constant {a q : ℚ} {w : ℤ} (hq : PadicLower p w q) :
    LaurentPadicLower p a w (RatFunc.C q) := by
  intro j
  change PadicLower p (w-j) ((rationalLaurentAt a (RatFunc.C q)).coeff j)
  rw [rationalLaurentAt_C, HahnSeries.C_apply]
  by_cases hj : j=0
  · simpa [hj, HahnSeries.C] using hq
  · simp [HahnSeries.C, hj, PadicLower]

theorem LaurentPadicLower.one (a : ℚ) : LaurentPadicLower p a 0 1 := by
  simpa using (LaurentPadicLower.constant (a:=a) (PadicLower.natCast (p:=p) 1))

theorem LaurentPadicLower.pow {a : ℚ} {w : ℤ} {f : RatFunc ℚ}
    (hf : LaurentPadicLower p a w f) (m : ℕ) :
    LaurentPadicLower p a ((m:ℤ)*w) (f^m) := by
  induction m with
  | zero => simpa using LaurentPadicLower.one (p:=p) a
  | succ m ih => simpa [pow_succ, add_mul] using ih.mul hf

theorem LaurentPadicLower.prod {ι : Type*} (s : Finset ι) (a : ℚ)
    (w : ι → ℤ) (f : ι → RatFunc ℚ)
    (hf : ∀ i ∈ s, LaurentPadicLower p a (w i) (f i)) :
    LaurentPadicLower p a (∑ i ∈ s, w i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LaurentPadicLower.one (p:=p) a
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hf i (by simp)).mul (ih (fun j hj => hf j (by simp [hj])))

def rootResidueWeight (p : ℕ) (z : ℤ) : ℤ := if p ∣ z.natAbs then 1 else 0

theorem rootResidueWeight_bounds (z : ℤ) :
    0 ≤ rootResidueWeight p z ∧ rootResidueWeight p z ≤ 1 := by
  unfold rootResidueWeight
  split_ifs <;> omega

theorem rootResidueWeight_padicVal (z : ℤ) (hz : z ≠ 0) (hs : z.natAbs < p^2) :
    padicValRat p (z:ℚ) = rootResidueWeight p z := by
  have hn : 0<z.natAbs := Int.natAbs_pos.mpr hz
  have hle := padicValNat_lt_square_le_one (p:=p) z.natAbs hn hs
  simp only [padicValRat.of_int, padicValInt, rootResidueWeight]
  split_ifs with hd
  · have hge := one_le_padicValNat_of_dvd (p:=p) (by omega : z.natAbs≠0) hd
    norm_cast
    omega
  · simp [padicValNat.eq_zero_of_not_dvd hd]

/-- Every integer linear numerator factor has the required residue weight. -/
theorem linearFactor_laurentPadicLower (a t : ℤ) :
    LaurentPadicLower p (a:ℚ) (rootResidueWeight p (a-t))
      (algebraMap ℚ[X] (RatFunc ℚ) (X-C (t:ℚ))) := by
  intro j
  cases j with
  | negSucc k =>
    rw [rationalCoefficientAt_polynomial_neg _ _ _ (by omega)]
    exact PadicLower.zero _
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast]
    rw [rationalCoefficientAt_polynomial]
    by_cases hk : k=0
    · subst k
      simp only [Polynomial.taylor_coeff_zero, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, Int.ofNat_zero, sub_zero]
      by_cases hat : a=t
      · simp [hat, PadicLower]
      right
      rw [← Int.cast_sub, padicValRat.of_int]
      unfold rootResidueWeight padicValInt
      split_ifs with hd
      · exact_mod_cast one_le_padicValNat_of_dvd (p:=p)
          (Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr hat)) hd
      · exact Int.natCast_nonneg _
    · by_cases hk1 : k=1
      · subst k
        simp only [map_sub, Polynomial.taylor_X, Polynomial.taylor_C,
          Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_one,
          Polynomial.coeff_C_succ, add_zero, sub_zero]
        right
        simp only [padicValRat.one]
        have h := (rootResidueWeight_bounds (p:=p) (a-t)).2
        omega
      · have he : ((X-C (t:ℚ)).taylor (a:ℚ)).coeff k = 0 := by
          simp only [map_sub, Polynomial.taylor_X, Polynomial.taylor_C,
            Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
          simp [hk, hk1, Ne.symm hk, Ne.symm hk1]
        rw [he]
        exact PadicLower.zero _

/-- A denominator root contributes the opposite weight. The square threshold
ensures a nonzero root difference contains at most one power of p. -/
theorem inverseLinearFactor_laurentPadicLower (a t : ℤ)
    (hs : (a-t).natAbs < p^2) :
    LaurentPadicLower p (a:ℚ) (-rootResidueWeight p (a-t)) (rationalPole (t:ℚ) 1) := by
  intro j
  by_cases hat : a=t
  · subst t
    rw [rationalCoefficientAt_pole_self]
    by_cases hj : j = -1
    · subst j
      simp [rootResidueWeight, PadicLower]
    · simp [hj, PadicLower]
  have hat' : (a:ℚ)≠(t:ℚ) := by exact_mod_cast hat
  cases j with
  | negSucc k =>
    rw [rationalCoefficientAt_pole_other_neg _ _ _ hat' _ (by omega)]
    exact PadicLower.zero _
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast]
    rw [show (1:ℕ)=0+1 from rfl, rationalCoefficientAt_pole_regular _ _ hat']
    simp only [zero_add, Nat.choose_self, Nat.cast_one, mul_one]
    right
    rw [padicValRat.div (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (sub_ne_zero.mpr hat'))]
    simp only [padicValRat.pow, padicValRat.neg, padicValRat.one, mul_zero, zero_sub]
    rw [← Int.cast_sub, rootResidueWeight_padicVal (a-t) (sub_ne_zero.mpr hat) hs]
    have h := (rootResidueWeight_bounds (p:=p) (a-t)).2
    push_cast
    nlinarith
end OddZeta.FourValue

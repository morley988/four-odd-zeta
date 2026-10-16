import FourValueCancelledWeight
import FourValueTaylorDenominators

noncomputable section
namespace OddZeta.FourValue
open Polynomial
open scoped LaurentSeries RatFunc
variable {p : ℕ} [Fact p.Prime]

def UniformLaurentPadicLower (p : ℕ) (a : ℚ) (w : ℤ) (f : RatFunc ℚ) : Prop :=
  ∀ j : ℤ, PadicLower p w (rationalCoefficientAt a j f)

theorem UniformLaurentPadicLower.mul {a : ℚ} {w v : ℤ} {f g : RatFunc ℚ}
    (hf : UniformLaurentPadicLower p a w f) (hg : UniformLaurentPadicLower p a v g) :
    UniformLaurentPadicLower p a (w+v) (f*g) := by
  intro j
  change PadicLower p (w+v) ((rationalLaurentAt a (f*g)).coeff j)
  rw [map_mul,HahnSeries.coeff_mul]
  exact padicLower_sum _ _ _ (fun ij hij => (hf ij.1).mul (hg ij.2))

theorem UniformLaurentPadicLower.constant {a q : ℚ} {w : ℤ} (hq : PadicLower p w q) :
    UniformLaurentPadicLower p a w (RatFunc.C q) := by
  intro j
  change PadicLower p w ((rationalLaurentAt a (RatFunc.C q)).coeff j)
  rw [rationalLaurentAt_C,HahnSeries.C_apply]
  by_cases hj : j=0
  · simpa [hj,HahnSeries.C] using hq
  · simp [HahnSeries.C,hj,PadicLower]

theorem UniformLaurentPadicLower.polynomial {w : ℤ} {P : ℚ[X]}
    (hP : PolynomialPadicLower p w P) (a : ℤ) :
    UniformLaurentPadicLower p (a:ℚ) w (algebraMap ℚ[X] (RatFunc ℚ) P) := by
  intro j
  cases j with
  | negSucc k =>
    rw [rationalCoefficientAt_polynomial_neg _ _ _ (by omega)]
    exact PadicLower.zero _
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast]
    rw [rationalCoefficientAt_polynomial]
    exact hP.taylor a k

theorem inverseLinearFactor_uniformLaurent (a t : ℤ)
    (ht : a=t ∨ ¬(p:ℤ)∣a-t) :
    UniformLaurentPadicLower p (a:ℚ) 0 (rationalPole (t:ℚ) 1) := by
  intro j
  by_cases hat : a=t
  · subst t
    rw [rationalCoefficientAt_pole_self]
    split_ifs <;> simp [PadicLower]
  have hd := ht.resolve_left hat
  have hv : padicValRat p ((a:ℚ)-(t:ℚ))=0 := by
    rw [← Int.cast_sub,padicValRat.of_int]
    simp only [padicValInt,padicValNat.eq_zero_of_not_dvd (by simpa only [Int.natCast_dvd] using hd),Nat.cast_zero]
  have hat' : (a:ℚ)≠(t:ℚ) := by exact_mod_cast hat
  cases j with
  | negSucc k =>
    rw [rationalCoefficientAt_pole_other_neg _ _ _ hat' _ (by omega)]
    exact PadicLower.zero _
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast]
    rw [show (1:ℕ)=0+1 from rfl,rationalCoefficientAt_pole_regular _ _ hat']
    simp only [zero_add,Nat.choose_self,Nat.cast_one,mul_one]
    right
    rw [padicValRat.div (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (sub_ne_zero.mpr hat'))]
    simp [hv]

theorem inverseIntegerRootProduct_uniformLaurent (a : ℤ) (roots : List ℤ)
    (hr : ∀ t∈roots,a=t ∨ ¬(p:ℤ)∣a-t) :
    UniformLaurentPadicLower p (a:ℚ) 0
      ((algebraMap ℚ[X] (RatFunc ℚ) (linearRootProduct (roots.map (fun z : ℤ => (z:ℚ)))))⁻¹) := by
  induction roots with
  | nil => simpa [linearRootProduct] using
      UniformLaurentPadicLower.constant (a:=(a:ℚ)) (PadicLower.natCast (p:=p) 1)
  | cons t ts ih =>
    have h := (inverseLinearFactor_uniformLaurent a t (hr t (by simp))).mul
      (ih (fun z hz => hr z (by simp [hz])))
    simpa [linearRootProduct,rationalPole,mul_inv_rev,mul_comm] using h

theorem PolynomialPadicLower.comp_integral {w : ℤ} {P Q : ℚ[X]}
    (hP : PolynomialPadicLower p w P) (hQ : PolynomialPadicLower p 0 Q) :
    PolynomialPadicLower p w (P.comp Q) := by
  rw [P.as_sum_range_C_mul_X_pow]
  simp only [sum_comp,mul_comp,C_comp,pow_comp,X_comp]
  apply PolynomialPadicLower.sum
  intro i hi
  simpa using (PolynomialPadicLower.constant (hP i)).mul (hQ.pow i)

theorem physicalSubstitution_polynomialPadicLower {w : ℤ} {P : ℚ[X]}
    (hP : PolynomialPadicLower p w P) :
    PolynomialPadicLower p w ((P.comp (C 4*X)).comp (X^2)) := by
  have hx : PolynomialPadicLower p 0 (X : ℚ[X]) := by
    simpa using integerLinearFactor_polynomialPadicLower (p:=p) 0
  exact (hP.comp_integral (by simpa using
    (PolynomialPadicLower.constant (PadicLower.natCast (p:=p) 4)).mul hx)).comp_integral
    (by simpa using hx.pow 2)

theorem targetGapPolynomial_integral (n : ℕ) :
    PolynomialPadicLower p 0 (targetGapPolynomial (K:=ℚ) n) := by
  have h := integerRootProduct_polynomialPadicLower (p:=p)
    (poleWindow (100*n) \ poleWindow (67*n)).toList
  simpa [targetGapPolynomial,integerRootProduct,linearRootProduct] using h

theorem rationalPhysicalTest_uniformLaurent (n : ℕ) (a : ℤ) (P : ℚ[X]) (w : ℤ)
    (hP : PolynomialPadicLower p w P)
    (ha : ∀ t∈targetPoleList n,a=t ∨ ¬(p:ℤ)∣a-t) :
    UniformLaurentPadicLower p (a:ℚ) (targetNormalizationValuation p n+w)
      (rationalPhysicalTest n P) := by
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
    (UniformLaurentPadicLower.polynomial (physicalSubstitution_polynomialPadicLower hP) a)
  simpa [rationalPhysicalTest,targetNormalizedWeight_cancelled,div_eq_mul_inv] using h
end OddZeta.FourValue

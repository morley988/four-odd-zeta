import FourValueWeightedMinorTransfer

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem PolynomialPadicLower.add {w : ℤ} {P Q : ℚ[X]}
    (hP : PolynomialPadicLower p w P) (hQ : PolynomialPadicLower p w Q) :
    PolynomialPadicLower p w (P+Q) := by
  intro j
  rw [Polynomial.coeff_add]
  exact (hP j).add (hQ j)

theorem PolynomialPadicLower.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (w : ℤ)
    (hf : ∀ i∈s, PolynomialPadicLower p w (f i)) : PolynomialPadicLower p w (∑ i∈s,f i) := by
  intro j
  rw [Polynomial.finset_sum_coeff]
  exact padicLower_sum s _ w (fun i hi => hf i hi j)

theorem PolynomialPadicLower.pow {w : ℤ} {P : ℚ[X]}
    (hP : PolynomialPadicLower p w P) (k : ℕ) : PolynomialPadicLower p ((k:ℤ)*w) (P^k) := by
  induction k with
  | zero => simpa using PolynomialPadicLower.constant (PadicLower.natCast (p:=p) 1)
  | succ k ih => simpa [pow_succ, add_mul] using ih.mul hP

theorem PolynomialPadicLower.taylor {w : ℤ} {P : ℚ[X]}
    (hP : PolynomialPadicLower p w P) (a : ℤ) : PolynomialPadicLower p w (P.taylor (a:ℚ)) := by
  rw [P.as_sum_range_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, Polynomial.taylor_C, Polynomial.taylor_X]
  apply PolynomialPadicLower.sum
  intro i hi
  have hx : PolynomialPadicLower p 0 (X+C (a:ℚ)) := by
    simpa only [Int.cast_neg, map_neg, sub_neg_eq_add] using
      integerLinearFactor_polynomialPadicLower (p:=p) (-a)
  simpa using (PolynomialPadicLower.constant (hP i)).mul (hx.pow i)

theorem polynomial_translated_expansion (P : ℚ[X]) (c : ℚ) (d : ℕ) (hP : P.natDegree<d) :
    P = ∑ i : Fin d, C ((P.taylor c).coeff i.val)*(X-C c)^i.val := by
  have hd : (P.taylor c).natDegree<d := by simpa using hP
  have h := (P.taylor c).as_sum_range_C_mul_X_pow' hd
  have hh := congrArg (Polynomial.taylor (-c)) h
  simpa only [map_sum,Polynomial.taylor_mul,Polynomial.taylor_pow,Polynomial.taylor_C,Polynomial.taylor_X,
    Polynomial.taylor_taylor,neg_add_cancel,Polynomial.taylor_zero,map_neg,
    ← sub_eq_add_neg, ← Fin.sum_univ_eq_sum_range] using hh

theorem squareBasis_taylor_coefficient_padicLower (i j : ℕ) (a : ℤ) :
    PadicLower p (-(padicValNat p (2*i).factorial:ℤ))
      (((squareBasisPolynomial (K:=ℚ) i).taylor (a:ℚ)).coeff j) :=
  (PolynomialPadicLower.taylor (fun k => squareBasisPolynomial_coefficient_padicLower i k) a) j
end OddZeta.FourValue

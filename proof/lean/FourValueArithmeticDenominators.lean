import FourValueLocalRationalForm

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {p : ℕ} [Fact p.Prime]

def rationalPencilDenominator (lambda : Fin 4 → ℚ) : ℕ := ∏ i, (lambda i).den

theorem rationalPencilDenominator_pos (lambda : Fin 4 → ℚ) :
    0<rationalPencilDenominator lambda := by
  exact Finset.prod_pos (fun i hi => (lambda i).den_pos)

theorem rationalPencilDenominator_dvd (lambda : Fin 4 → ℚ) (i : Fin 4) :
    (lambda i).den ∣ rationalPencilDenominator lambda :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

/-- One fixed integer controls the four rational pencil parameters. -/
theorem rationalPencil_integral_at_prime (lambda : Fin 4 → ℚ)
    (hp : ¬p ∣ rationalPencilDenominator lambda) (i : Fin 4) :
    PadicLower p 0 (lambda i) := by
  have hd : ¬p∣(lambda i).den := fun h => hp (h.trans (rationalPencilDenominator_dvd lambda i))
  right
  simp only [padicValRat, padicValNat.eq_zero_of_not_dvd hd, Nat.cast_zero, sub_zero]
  exact Int.natCast_nonneg _

def PolynomialPadicLower (p : ℕ) (w : ℤ) (P : ℚ[X]) : Prop :=
  ∀ j, PadicLower p w (P.coeff j)

theorem PolynomialPadicLower.mul {v w : ℤ} {P Q : ℚ[X]}
    (hP : PolynomialPadicLower p v P) (hQ : PolynomialPadicLower p w Q) :
    PolynomialPadicLower p (v+w) (P*Q) := by
  intro j
  rw [Polynomial.coeff_mul]
  exact padicLower_sum _ _ _ (fun ij hij => (hP ij.1).mul (hQ ij.2))

theorem PolynomialPadicLower.constant {w : ℤ} {q : ℚ} (hq : PadicLower p w q) :
    PolynomialPadicLower p w (C q) := by
  intro j
  by_cases hj : j=0
  · simpa [hj] using hq
  · simp [Polynomial.coeff_C, hj, PadicLower]

theorem integerLinearFactor_polynomialPadicLower (z : ℤ) :
    PolynomialPadicLower p 0 (X-C (z:ℚ)) := by
  intro j
  by_cases hj : j=0
  · subst j
    simpa using (PadicLower.intCast (p:=p) z).neg
  · by_cases hj1 : j=1
    · subst j
      simpa only [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_C_succ, sub_zero, Nat.cast_one] using PadicLower.natCast (p:=p) 1
    · simp only [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X]
      simp [hj, Ne.symm hj, Ne.symm hj1, PadicLower]

theorem integerRootProduct_polynomialPadicLower (roots : List ℤ) :
    PolynomialPadicLower p 0 (linearRootProduct (roots.map (fun z : ℤ => (z:ℚ)))) := by
  induction roots with
  | nil =>
    simpa [linearRootProduct] using PolynomialPadicLower.constant (PadicLower.natCast (p:=p) 1)
  | cons z zs ih =>
    simpa [linearRootProduct] using (integerLinearFactor_polynomialPadicLower (p:=p) z).mul ih

theorem squareRootProduct_polynomialPadicLower (i : ℕ) :
    PolynomialPadicLower p 0 (squareRootProduct (K:=ℚ) i) := by
  have h := integerRootProduct_polynomialPadicLower (p:=p) ((List.range i).map (fun h : ℕ => (h:ℤ)^2))
  convert h using 1 <;> try rfl
  unfold squareRootProduct
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro x hx
  simp

/-- The precise factorial cost of the actual square basis, for every prime. -/
theorem squareBasisPolynomial_coefficient_padicLower (i j : ℕ) :
    PadicLower p (-(padicValNat p (2*i).factorial:ℤ))
      ((squareBasisPolynomial (K:=ℚ) i).coeff j) := by
  by_cases hi : i=0
  · subst i
    simpa [squareBasisPolynomial] using
      PolynomialPadicLower.constant (PadicLower.natCast (p:=p) 1) j
  have hfac : PadicLower p (-(padicValNat p (2*i).factorial:ℤ))
      (((2*i).factorial:ℚ)⁻¹) := by
    right
    simp
  have h := (PolynomialPadicLower.constant ((PadicLower.natCast (p:=p) 2).mul hfac)).mul
    (squareRootProduct_polynomialPadicLower (p:=p) i)
  simpa [squareBasisPolynomial, hi, div_eq_mul_inv] using h j

theorem squareBasisPolynomial_coefficient_padicLower_large (i j : ℕ) (hi : 2*i<p^2) :
    PadicLower p (-((2*i/p:ℕ):ℤ)) ((squareBasisPolynomial (K:=ℚ) i).coeff j) := by
  have h := squareBasisPolynomial_coefficient_padicLower (p:=p) i j
  rw [OddZeta.Coefficients.factorial_valuation_below_square p _ hi] at h
  exact h

theorem target_selected_factorial_lt_square (n : ℕ) (i : Fin (targetHankelDegree n+1))
    (hs : 800*n<p^2) : 2*i.val<p^2 := by
  have hi := i.isLt
  unfold targetHankelDegree at hi
  omega

/-- All selected basis coefficients have the advertised large-prime floor
cost; no bound on their factorial arguments is left as a hypothesis. -/
theorem target_squareBasis_coefficient_padicLower (n : ℕ)
    (i : Fin (targetHankelDegree n+1)) (j : ℕ) (hs : 800*n<p^2) :
    PadicLower p (-((2*i.val/p:ℕ):ℤ)) ((squareBasisPolynomial (K:=ℚ) i.val).coeff j) :=
  squareBasisPolynomial_coefficient_padicLower_large _ _ (target_selected_factorial_lt_square n i hs)
end OddZeta.FourValue

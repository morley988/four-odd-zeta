import FourValueRationalFamily
import FourValueLaurentObservations

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def tupleForwardPolynomial (b : ℕ) (a : Fin 15 → ℕ) : K[X] :=
  (X+C ((b+1:ℕ):K))^5 * ∏ i, (X-C (a i:K))

def tupleBackwardPolynomial (b : ℕ) (a : Fin 15 → ℕ) : K[X] :=
  (X-C (b:K))^5 * ∏ i, (X+C ((a i+1:ℕ):K))

theorem tuplePearson_forward (b : ℕ) (a : Fin 15 → ℕ) :
    (tuplePearsonPolynomial (K:=K) b a).comp (C 2*X) =
      C (2^20:K)*tupleForwardPolynomial b a := by
  have hp : (linearRootProduct (List.ofFn (fun i => 2*(a i:K)))).comp (C 2*X) =
      C (2^15:K)*∏ i,(X-C (a i:K)) := by
    simp only [linearRootProduct,List.map_ofFn,List.prod_ofFn,Function.comp_def,Polynomial.prod_comp,
      Polynomial.sub_comp,Polynomial.X_comp,Polynomial.C_comp]
    have heq : ∀ i : Fin 15,(C 2*X-C (2*(a i:K)):K[X])=C 2*(X-C (a i:K)) := by
      intro i
      rw [map_mul]
      ring
    simp_rw [heq]
    rw [Finset.prod_mul_distrib]
    simp [map_pow]
  rw [tuplePearsonPolynomial,Polynomial.mul_comp,Polynomial.pow_comp,
    Polynomial.add_comp,Polynomial.X_comp,Polynomial.C_comp,hp,tupleForwardPolynomial]
  have heq : (C 2*X+C (2*(b:K)+2):K[X])=C 2*(X+C ((b+1:ℕ):K)) := by
    simp only [Nat.cast_add,Nat.cast_one,map_add,map_mul,map_ofNat,map_one]
    ring
  rw [heq,mul_pow,← map_pow]
  norm_num only [map_pow,map_ofNat]
  ring

theorem tuplePearson_backward_shifted (b : ℕ) (a : Fin 15 → ℕ) :
    (tuplePearsonPolynomial (K:=K) b a).comp (-C 2*X-C 2) =
      C (2^20:K)*tupleBackwardPolynomial b a := by
  have hp : (linearRootProduct (List.ofFn (fun i => 2*(a i:K)))).comp (-C 2*X-C 2) =
      C ((-2)^15:K)*∏ i,(X+C ((a i+1:ℕ):K)) := by
    simp only [linearRootProduct,List.map_ofFn,List.prod_ofFn,Function.comp_def,Polynomial.prod_comp,
      Polynomial.sub_comp,Polynomial.X_comp,Polynomial.C_comp]
    have heq : ∀ i : Fin 15,(-C 2*X-C 2-C (2*(a i:K)):K[X])=
        C (-2)*(X+C ((a i+1:ℕ):K)) := by
      intro i
      simp only [Nat.cast_add,Nat.cast_one,map_add,map_mul,map_neg,map_ofNat,map_one]
      ring
    simp_rw [heq]
    rw [Finset.prod_mul_distrib]
    simp [map_pow]
  rw [tuplePearsonPolynomial,Polynomial.mul_comp,Polynomial.pow_comp,
    Polynomial.add_comp,Polynomial.X_comp,Polynomial.C_comp,hp,tupleBackwardPolynomial]
  have heq : (-C 2*X-C 2+C (2*(b:K)+2):K[X])=C (-2)*(X-C (b:K)) := by
    simp only [map_add,map_mul,map_neg,map_ofNat,map_one]
    ring
  rw [heq,mul_pow,← map_pow]
  norm_num only [map_pow,map_neg,map_ofNat]
  ring

def tupleEvenWeight (b : ℕ) (a : Fin 15 → ℕ) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (C 2*(centeredDenominator b)^5) /
    algebraMap K[X] (RatFunc K) (tupleDenominator a)

theorem tupleWeight_eq_X_even (b : ℕ) (a : Fin 15 → ℕ) :
    tupleWeight (K:=K) b a=RatFunc.X * tupleEvenWeight b a := by
  simp only [tupleWeight,tupleNumerator,tupleEvenWeight,map_mul,map_pow,RatFunc.algebraMap_X]
  ring

theorem centeredDenominator_rationalShift (b : ℕ) :
    rationalShift (1:K) (algebraMap K[X] (RatFunc K) (centeredDenominator b)) *
      algebraMap K[X] (RatFunc K) (X-C (b:K)) =
      algebraMap K[X] (RatFunc K) (centeredDenominator b) *
        algebraMap K[X] (RatFunc K) (X+C ((b+1:ℕ):K)) := by
  rw [rationalShift_polynomial,← map_mul,← map_mul]
  congr 1
  simpa [Polynomial.taylor_apply] using centeredDenominator_shift (K:=K) b

theorem tupleDenominator_shift (a : Fin 15 → ℕ) :
    rationalShift (1:K) (algebraMap K[X] (RatFunc K) (tupleDenominator a)) *
      (∏ i,algebraMap K[X] (RatFunc K) (X-C (a i:K))) =
      algebraMap K[X] (RatFunc K) (tupleDenominator a) *
        ∏ i,algebraMap K[X] (RatFunc K) (X+C ((a i+1:ℕ):K)) := by
  simp only [tupleDenominator,map_prod,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact centeredDenominator_rationalShift (a i)

theorem tupleEvenWeight_shift (b : ℕ) (a : Fin 15 → ℕ) :
    rationalShift (1:K) (tupleEvenWeight b a) *
      algebraMap K[X] (RatFunc K) (tupleBackwardPolynomial b a) =
      tupleEvenWeight b a * algebraMap K[X] (RatFunc K) (tupleForwardPolynomial b a) := by
  have hd : algebraMap K[X] (RatFunc K) (tupleDenominator (K:=K) a)≠0 :=
    RatFunc.algebraMap_ne_zero (tupleDenominator_monic a).ne_zero
  have hs : rationalShift (1:K) (algebraMap K[X] (RatFunc K) (tupleDenominator (K:=K) a))≠0 :=
    by simpa using (rationalShift (1:K)).injective.ne hd
  have hn := congrArg (fun f : RatFunc K => f^5) (centeredDenominator_rationalShift (K:=K) b)
  rw [mul_pow,mul_pow] at hn
  have hD := tupleDenominator_shift (K:=K) a
  simp only [tupleEvenWeight,tupleBackwardPolynomial,tupleForwardPolynomial,
    map_div₀,map_mul,map_pow,map_prod] at *
  have htwo : rationalShift (1:K) (algebraMap K[X] (RatFunc K) (C 2))=2 := by
    rw [Polynomial.C_ofNat,map_ofNat,map_ofNat]
  rw [htwo]
  simp only [Polynomial.C_ofNat,map_ofNat]
  field_simp
  linear_combination     (∏ i,algebraMap K[X] (RatFunc K) (X+C ((a i+1:ℕ):K))) *
    algebraMap K[X] (RatFunc K) (tupleDenominator a) * hn -
    (algebraMap K[X] (RatFunc K) (centeredDenominator b))^5 *
    (algebraMap K[X] (RatFunc K) (X+C ((b+1:ℕ):K)))^5 * hD

end OddZeta.FourValue

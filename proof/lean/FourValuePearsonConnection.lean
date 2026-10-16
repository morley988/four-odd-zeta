import FourValuePearsonBoundary
import FourValueRationalPearson
import FourValueCoefficientDifference

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def tupleEndpointDenominator (a : Fin 15 → ℕ) : K[X] := ∏ i,endpointDenominator (a i)

theorem tupleEndpointDenominator_monic (a : Fin 15 → ℕ) :
    (tupleEndpointDenominator (K:=K) a).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun i _ => endpointDenominator_monic (a i))

theorem tuplePadding_product (b : ℕ) (a : Fin 15 → ℕ) (ha : ∀ i,a i≤b) :
    tuplePadding (K:=K) b a * tupleEndpointDenominator a=(endpointDenominator b)^15 := by
  rw [tuplePadding,tupleEndpointDenominator,← Finset.prod_mul_distrib]
  simp_rw [endpointPadding_mul _ _ (ha _)]
  simp

theorem tupleDenominator_endpoint_factor (a : Fin 15 → ℕ) :
    tupleDenominator (K:=K) a=(∏ i,(X-C (a i:K)))*tupleEndpointDenominator a := by
  simp only [tupleDenominator,centeredDenominator_endpoint_factor,Finset.prod_mul_distrib,
    tupleEndpointDenominator]

theorem tupleEvenWeight_forward_cancel (b : ℕ) (a : Fin 15 → ℕ) :
    tupleEvenWeight (K:=K) b a * algebraMap K[X] (RatFunc K) (tupleForwardPolynomial b a) =
      2*(algebraMap K[X] (RatFunc K) (centeredDenominator b))^5 *
        (algebraMap K[X] (RatFunc K) (X+C ((b+1:ℕ):K)))^5 /
          algebraMap K[X] (RatFunc K) (tupleEndpointDenominator a) := by
  have hD : algebraMap K[X] (RatFunc K) (tupleEndpointDenominator (K:=K) a)≠0 :=
    RatFunc.algebraMap_ne_zero (tupleEndpointDenominator_monic a).ne_zero
  have hU : algebraMap K[X] (RatFunc K) (∏ i : Fin 15,(X-C (a i:K)))≠0 :=
    RatFunc.algebraMap_ne_zero (Polynomial.monic_prod_of_monic _ _
      (fun i _ => Polynomial.monic_X_sub_C (a i:K))).ne_zero
  rw [tupleEvenWeight,tupleDenominator_endpoint_factor,tupleForwardPolynomial]
  simp only [map_mul,map_pow,Polynomial.C_ofNat,map_ofNat]
  field_simp

theorem pearsonBoundaryFunction_eq (b : ℕ) (a : Fin 15 → ℕ) (q : K[X])
    (ha : ∀ i,a i≤b) :
    pearsonBoundaryFunction b a q = (2^20:RatFunc K)*tupleEvenWeight b a *
      algebraMap K[X] (RatFunc K) (tupleForwardPolynomial b a) *
      algebraMap K[X] (RatFunc K) (q.comp ((C 2*X+1)^2)) := by
  have hD : algebraMap K[X] (RatFunc K) (tupleEndpointDenominator (K:=K) a)≠0 :=
    RatFunc.algebraMap_ne_zero (tupleEndpointDenominator_monic a).ne_zero
  have hR : algebraMap K[X] (RatFunc K) (endpointDenominator (K:=K) b)≠0 :=
    RatFunc.algebraMap_ne_zero (endpointDenominator_monic b).ne_zero
  have hpad := congrArg (algebraMap K[X] (RatFunc K)) (tuplePadding_product (K:=K) b a ha)
  simp only [map_mul,map_pow] at hpad
  rw [mul_assoc (2^20) (tupleEvenWeight b a),tupleEvenWeight_forward_cancel]
  rw [pearsonBoundaryFunction,pearsonBoundaryNumerator,centeredDenominator_endpoint_factor]
  simp only [map_mul,map_pow,Polynomial.C_ofNat,map_ofNat]
  field_simp
  linear_combination     (algebraMap K[X] (RatFunc K) (X-C (b:K)))^5 *
    (algebraMap K[X] (RatFunc K) (X+C ((b+1:ℕ):K)))^5 *
    algebraMap K[X] (RatFunc K) (q.comp ((2*X+1)^2)) * hpad

end OddZeta.FourValue

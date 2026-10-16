import FourValueArithmeticBoundary

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def targetReducedDenominator (n : ℕ) : K[X] :=
  ∏ i : Fin 10, centeredDenominator (targetFactorialEndpoints i*n)

def targetGapPolynomial (n : ℕ) : K[X] :=
  integerRootProduct (poleWindow (100*n) \ poleWindow (67*n))

theorem targetDenominator_cancel_five (n : ℕ) :
    tupleDenominator (K:=K) (targetEndpointTuple n) =
      (centeredDenominator (67*n))^5 * targetReducedDenominator n := by
  simp [tupleDenominator,targetEndpointTuple,targetFactorialEndpoints,targetReducedDenominator,
    Fin.prod_univ_succ, Nat.mul_comm]
  ring

theorem targetGapPolynomial_factor (n : ℕ) :
    centeredDenominator (K:=K) (100*n) = centeredDenominator (67*n)*targetGapPolynomial n := by
  rw [centeredDenominator_integerProduct,centeredDenominator_integerProduct]
  unfold targetGapPolynomial integerRootProduct
  symm
  rw [mul_comm]
  apply Finset.prod_sdiff
  intro a ha
  simp only [poleWindow,Finset.mem_Icc] at ha ⊢
  omega

theorem targetNormalizedWeight_cancelled (n : ℕ) :
    targetNormalizedWeight (K:=K) n =
      RatFunc.C (targetNormalization n) *
      (algebraMap K[X] (RatFunc K) (C 2*X*(targetGapPolynomial n)^5) /
        algebraMap K[X] (RatFunc K) (targetReducedDenominator n)) := by
  unfold targetNormalizedWeight tupleWeight tupleNumerator
  rw [targetDenominator_cancel_five,targetGapPolynomial_factor]
  have hd : algebraMap K[X] (RatFunc K) (centeredDenominator (K:=K) (67*n)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (centeredDenominator_monic _).ne_zero
  simp only [map_mul,map_pow]
  field_simp

/-- Actual integer poles with multiplicities after cancelling the five
repeated endpoints. The signed list is useful both for jets and valuations. -/
def targetPoleList (n : ℕ) : List ℤ :=
  (List.ofFn (fun i : Fin 10 => (poleWindow (targetFactorialEndpoints i*n)).toList)).flatten

theorem targetReducedDenominator_list (n : ℕ) :
    targetReducedDenominator (K:=K) n =
      linearRootProduct ((targetPoleList n).map (fun z : ℤ => (z:K))) := by
  simp [targetReducedDenominator,centeredDenominator_integerProduct,integerRootProduct,
    linearRootProduct,targetPoleList,List.map_flatten,List.prod_flatten,List.map_map,
    Function.comp_def,List.prod_ofFn, Fin.prod_univ_succ]

theorem targetPoleList_bound (n : ℕ) (a : ℤ) (ha : a∈targetPoleList n) :
    a∈poleWindow (63*n) := by
  simp only [targetPoleList,List.mem_flatten,List.mem_ofFn] at ha
  obtain ⟨s,⟨i,rfl⟩,ha⟩ := ha
  have hi := targetFactorialEndpoints_le i
  simp only [Finset.mem_toList,poleWindow,Finset.mem_Icc] at ha ⊢
  have hh : targetFactorialEndpoints i*n ≤ 63*n := Nat.mul_le_mul_right n hi
  omega
end OddZeta.FourValue

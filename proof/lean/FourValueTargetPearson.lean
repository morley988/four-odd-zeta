import FourValueConcretePearson

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def targetEndpointTuple (n : ℕ) : Fin 15 → ℕ :=
  ![67*n,67*n,67*n,67*n,67*n,63*n,60*n,58*n,57*n,54*n,52*n,49*n,47*n,44*n,42*n]

theorem targetEndpointTuple_bounded (n : ℕ) (i : Fin 15) : targetEndpointTuple n i≤100*n := by
  fin_cases i <;> simp [targetEndpointTuple] <;> omega

theorem targetEndpointTuple_beta (n : ℕ) : tupleBeta (100*n) (targetEndpointTuple n)=361*(n:ℤ) := by
  norm_num [tupleBeta,targetEndpointTuple,Fin.sum_univ_succ]
  ring

theorem targetEndpointTuple_pearson (n : ℕ) :
    tuplePearsonPolynomial (K:=K) (100*n) (targetEndpointTuple n)=pearsonPolynomial (n:K) := by
  have hroots : List.ofFn (fun i => 2*(targetEndpointTuple n i:K))=physicalEndpointRoots (n:K) := by
    norm_num [targetEndpointTuple,List.ofFn_succ,physicalEndpointRoots]
    and_intros <;> first | trivial | ring
  rw [tuplePearsonPolynomial,pearsonPolynomial,hroots]
  congr 3
  push_cast
  ring

theorem targetNine_pearson (n : ℕ) (q : K[X]) (hq : (q.natDegree:ℤ)+6≤361*(n:ℤ))
    (j : Fin 9) :
    observedTupleFunctional (nineRationalObservations (100*n)) (100*n) (targetEndpointTuple n) j
      ((pearsonOperator (pearsonPolynomial (n:K)) q).comp (C 4*X))=0 := by
  rw [← targetEndpointTuple_pearson]
  apply nineRationalObservations_pearson _ _ (targetEndpointTuple_bounded n) q _ j
  simpa [targetEndpointTuple_beta] using hq

theorem targetNine_pearson_monomial (n k : ℕ) (hk : k+6≤361*n) (j : Fin 9) :
    observedTupleFunctional (nineRationalObservations (K:=K) (100*n)) (100*n) (targetEndpointTuple n) j
      ((pearsonOperator (pearsonPolynomial (n:K)) (X^k)).comp (C 4*X))=0 := by
  apply targetNine_pearson n (X^k) _ j
  simpa using (show (k:ℤ)+6≤361*(n:ℤ) by exact_mod_cast hk)

end OddZeta.FourValue

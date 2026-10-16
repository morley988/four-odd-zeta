import FourValueRationalFamily
import FourValueMomentCompanion
import FourValueTuplePaths
import Mathlib.Tactic

/-! Assemble the endpoint argument for linear observations of the actual
rational weight. The observation identities and seed independence are
explicit remaining inputs. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def tupleMomentRelation (b : ℕ) (a : Fin 15 → ℕ) : K[X] :=
  (pearsonOperator (tuplePearsonPolynomial b a) 1).comp (C 4*X)

theorem tupleMomentRelation_degree (b : ℕ) (a : Fin 15 → ℕ)
    (hbeta : 6≤tupleBeta b a) : (tupleMomentRelation (K:=K) b a).natDegree=9 := by
  rw [tupleMomentRelation,Polynomial.natDegree_comp,tuplePearson_relation_degree b a hbeta,
    Polynomial.natDegree_C_mul (by norm_num : (4:K)≠0),Polynomial.natDegree_X,mul_one]

theorem tupleMomentRelation_endpoint_nonzero (b : ℕ) (a : Fin 15 → ℕ)
    (i : Fin 15) (hi : 0<a i) (hib : a i≤b) :
    (tupleMomentRelation (K:=K) b a).eval ((a i:K)^2)≠0 := by
  rw [tupleMomentRelation,Polynomial.eval_comp]
  simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    mul_pow,show (2:K)^2=4 by norm_num] using
      tuplePearson_relation_endpoint_nonzero (K:=K) b a i hi hib

def observedTupleFunctional {ι : Type*} (obs : ι → RatFunc K →ₗ[K] K)
    (b : ℕ) (a : Fin 15 → ℕ) (j : ι) : K[X] →ₗ[K] K :=
  (obs j).comp (tupleRationalTest b a)

theorem observedTuple_endpoint_initial (b : ℕ) (a : Fin 15 → ℕ) (i : Fin 15)
    {ι : Type*} (obs : ι → RatFunc K →ₗ[K] K) :
    (fun j => shiftedInitialMoments
      (observedTupleFunctional obs b (Function.update a i (a i+1)) j) (((a i+1:ℕ):K)^2)) =
      (fun j => initialMoments (observedTupleFunctional obs b a j)) := by
  funext j k
  change obs j (tupleRationalTest b (Function.update a i (a i+1))
    ((X-C (((a i+1:ℕ):K)^2))*X^k.val)) = obs j (tupleRationalTest b a (X^k.val))
  rw [tupleRationalTest_endpoint_step]

/-- One endpoint step preserves the nine initial-vector independence
statement for actual observations of the rational-function family. -/
theorem observedTuple_independence_step {ι : Type*} [Fintype ι]
    (obs : ι → RatFunc K →ₗ[K] K) (b : ℕ) (a : Fin 15 → ℕ)
    (i : Fin 15) (hi : a i<b) (hbeta : 6≤tupleBeta b a)
    (hrel : ∀ j, observedTupleFunctional obs b (Function.update a i (a i+1)) j
      (tupleMomentRelation b (Function.update a i (a i+1)))=0) :
    LinearIndependent K (fun j => initialMoments
      (observedTupleFunctional obs b (Function.update a i (a i+1)) j)) ↔
    LinearIndependent K (fun j => initialMoments (observedTupleFunctional obs b a j)) := by
  let a' := Function.update a i (a i+1)
  have hb' : 6≤tupleBeta b a' := by
    dsimp [a']
    rw [tupleBeta_update_succ]
    omega
  have hp := tupleMomentRelation_degree (K:=K) b a' hb'
  have hpa : (tupleMomentRelation (K:=K) b a').eval (((a i+1:ℕ):K)^2)≠0 := by
    simpa [a'] using tupleMomentRelation_endpoint_nonzero (K:=K) b a' i
      (by simp [a']) (by simp only [a',Function.update_self]; omega)
  have h := endpoint_initial_independence_iff
    (observedTupleFunctional obs b a') (tupleMomentRelation b a') hp
    (((a i+1:ℕ):K)^2) hpa hrel
  change LinearIndependent K (fun j => shiftedInitialMoments
      (observedTupleFunctional obs b (Function.update a i (a i+1)) j) (((a i+1:ℕ):K)^2)) ↔ _ at h
  rw [observedTuple_endpoint_initial] at h
  exact h.symm

/-- The whole endpoint deformation is now checked for the actual weights.
What remains to instantiate this is the Pearson relation for the chosen
observations and their initial-vector independence at the seed. -/
theorem observedTuple_independence_of_seed {ι : Type*} [Fintype ι]
    (obs : ι → RatFunc K →ₗ[K] K) (b : ℕ) (hb : 6≤b)
    (hrel : ∀ a, (∀ i,a i≤b) → 6≤tupleBeta b a →
      ∀ j,observedTupleFunctional obs b a j (tupleMomentRelation b a)=0)
    (hseed : LinearIndependent K (fun j => initialMoments
      (observedTupleFunctional obs b (seedTuple b) j)))
    (a : Fin 15 → ℕ) (ha : ∀ i,a i≤b) (hbeta : 6≤tupleBeta b a) :
    LinearIndependent K (fun j => initialMoments (observedTupleFunctional obs b a j)) := by
  apply admissible_tuple_property_of_seed b hb
    (fun a => LinearIndependent K (fun j => initialMoments (observedTupleFunctional obs b a j)))
    ?_ hseed a ha hbeta
  intro a ha hbeta i hi
  apply observedTuple_independence_step obs b a i hi hbeta
  exact hrel _ (tuple_update_succ_bounded b a ha i hi)
    (by rw [tupleBeta_update_succ]; omega)

theorem tupleDenominator_seed (b : ℕ) :
    tupleDenominator (K:=K) (seedTuple b)=(centeredDenominator b)^6*X^9 := by
  norm_num [tupleDenominator,seedTuple,Fin.prod_univ_succ]
  ring

/-- The rational weight at the seed is exactly the function used in the
seed block calculation, without an unspecified nonzero scalar. -/
theorem tupleWeight_seed (b : ℕ) :
    tupleWeight (K:=K) b (seedTuple b)=
      (2:RatFunc K)/((algebraMap K[X] (RatFunc K) X)^8 *
        algebraMap K[X] (RatFunc K) (centeredDenominator b)) := by
  have hD : algebraMap K[X] (RatFunc K) (centeredDenominator (K:=K) b)≠0 :=
    RatFunc.algebraMap_ne_zero (centeredDenominator_monic b).ne_zero
  have hX : algebraMap K[X] (RatFunc K) X≠0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  rw [tupleWeight,tupleDenominator_seed,tupleNumerator]
  simp only [map_mul,map_pow,map_ofNat,Polynomial.C_ofNat]
  field_simp

end OddZeta.FourValue

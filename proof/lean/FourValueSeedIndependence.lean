import FourValueSeedPoles
import FourValueSeedTailBlock
import FourValueTargetPearson

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def seedObservationMatrix (b : ℕ) : Matrix (Fin 9) (Fin 9) K :=
  fun i j => nineRationalObservations b i (tupleRationalTest b (seedTuple b) (X^j.val))

theorem seedObservationMatrix_B (b : ℕ) (i : Fin 4) (j : Fin 9) :
    seedObservationMatrix (K:=K) b ⟨3-i.val,by omega⟩ j =
      rationalB b (9-2*i.val) (tupleRationalTest b (seedTuple b) (X^j.val)) := by
  fin_cases i <;> rfl

theorem seedObservationMatrix_C (b : ℕ) (i : Fin 5) (j : Fin 9) :
    seedObservationMatrix (K:=K) b (Fin.natAdd 4 i) j =
      rationalC b i.val (tupleRationalTest b (seedTuple b) (X^j.val)) := by
  fin_cases i <;> rfl

theorem seedObservationMatrix_kernel (b : ℕ) (hb : 5≤b) (v : Fin 9 → K)
    (hz : (seedObservationMatrix b).mulVec v=0) : v=0 := by
  have hlo : (fun i : Fin 4 => v (Fin.castAdd 5 i))=0 := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr (seedBMatrix_isUnit b))
    rw [Matrix.mulVec_zero]
    funext i
    have hi := congrFun hz (⟨3-i.val,by omega⟩:Fin 9)
    simp only [Matrix.mulVec,dotProduct,Pi.zero_apply,seedObservationMatrix_B] at hi
    rw [Fin.sum_univ_add (a:=4) (b:=5)] at hi
    have ht : (∑ j : Fin 5, rationalB b (9-2*i.val)
        (tupleRationalTest b (seedTuple b) (X^(Fin.natAdd 4 j).val))*v (Fin.natAdd 4 j))=0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [show (Fin.natAdd 4 j).val=j.val+4 by simp [Nat.add_comm],
        seed_tail_B_zero b hb j _ (by omega),zero_mul]
    rw [ht,add_zero] at hi
    exact hi
  have hhi : (fun i : Fin 5 => v (Fin.natAdd 4 i))=0 := by
    apply seed_tail_C_kernel b hb
    intro i
    have hi := congrFun hz (Fin.natAdd 4 i)
    simp only [Matrix.mulVec,dotProduct,Pi.zero_apply,seedObservationMatrix_C] at hi
    rw [Fin.sum_univ_add (a:=4) (b:=5)] at hi
    have ht : (∑ j : Fin 4, rationalC b i.val
        (tupleRationalTest b (seedTuple b) (X^(Fin.castAdd 5 j).val))*v (Fin.castAdd 5 j))=0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [congrFun hlo j,Pi.zero_apply,mul_zero]
    rw [ht,zero_add] at hi
    simpa only [Fin.val_natAdd,Nat.add_comm,mul_comm] using hi
  funext i
  exact Fin.addCases (motive:=fun i => v i=0) (fun j => congrFun hlo j) (fun j => congrFun hhi j) i

theorem seedObservationMatrix_isUnit (b : ℕ) (hb : 5≤b) :
    IsUnit (seedObservationMatrix (K:=K) b) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w h
  apply sub_eq_zero.mp
  apply seedObservationMatrix_kernel b hb
  rw [Matrix.mulVec_sub,h,sub_self]

/-- Unconditional independence of the nine concrete seed observation vectors. -/
theorem concreteNine_seed_independence (b : ℕ) (hb : 5≤b) :
    LinearIndependent K (fun j => initialMoments
      (observedTupleFunctional (nineRationalObservations (K:=K) b) b (seedTuple b) j)) := by
  exact Matrix.linearIndependent_rows_iff_isUnit.mpr (seedObservationMatrix_isUnit b hb)

/-- All seed and Pearson inputs have now been proved for the concrete observations. -/
theorem concreteNine_independence (b : ℕ) (hb : 6≤b)
    (a : Fin 15 → ℕ) (ha : ∀ i,a i≤b) (hbeta : 6≤tupleBeta b a) :
    LinearIndependent K (fun j => initialMoments
      (observedTupleFunctional (nineRationalObservations (K:=K) b) b a j)) := by
  exact concreteNine_independence_of_seed b hb (concreteNine_seed_independence b (by omega))
    a ha hbeta

/-- The specified four-value tuple has nine independent concrete observation vectors. -/
theorem targetNine_independence (n : ℕ) (hn : 1≤n) :
    LinearIndependent K (fun j => initialMoments
      (observedTupleFunctional (nineRationalObservations (K:=K) (100*n))
        (100*n) (targetEndpointTuple n) j)) := by
  apply concreteNine_independence (100*n) (by omega) _ (targetEndpointTuple_bounded n)
  rw [targetEndpointTuple_beta]
  have hn' : (1:ℤ)≤(n:ℤ) := by exact_mod_cast hn
  omega

end OddZeta.FourValue

import FourValueLaurentObservations
import FourValueCenteredProducts
import Mathlib.Algebra.Polynomial.PartialFractions

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def integerRootProduct (S : Finset ℤ) : K[X] := ∏ j ∈ S, (X-C (j:K))

theorem integerRootProduct_monic (S : Finset ℤ) : (integerRootProduct (K:=K) S).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)

theorem integerRootProduct_degree (S : Finset ℤ) :
    (integerRootProduct (K:=K) S).natDegree=S.card := by
  rw [integerRootProduct,Polynomial.natDegree_prod_of_monic S (fun (j:ℤ) => X-C (j:K))
    (fun j _ => Polynomial.monic_X_sub_C (j:K))]
  simp only [Polynomial.natDegree_X_sub_C]
  simp

theorem integerRootProduct_eval_zero_iff (S : Finset ℤ) (x : K) :
    (integerRootProduct S).eval x=0 ↔ ∃ j ∈ S, x=(j:K) := by
  simp [integerRootProduct,Polynomial.eval_prod,Finset.prod_eq_zero_iff,sub_eq_zero]

theorem centeredDenominator_integerProduct (b : ℕ) :
    centeredDenominator (K:=K) b=integerRootProduct (poleWindow b) := by
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (integerRootProduct_monic _) (centeredDenominator_monic b)
  · apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      exact Polynomial.pairwise_coprime_X_sub_C (Int.cast_injective) hij
    · intro j hj
      apply Polynomial.dvd_iff_isRoot.mpr
      apply (centeredDenominator_eval_zero_iff b (j:K)).mpr
      exact ⟨j,(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2,rfl⟩
  · rw [centeredDenominator_degree,integerRootProduct_degree,poleWindow,Int.card_Icc]
    omega

def endpointDenominator (b : ℕ) : K[X] := integerRootProduct (Finset.Ico (-(b:ℤ)) b)

theorem endpointDenominator_monic (b : ℕ) : (endpointDenominator (K:=K) b).Monic :=
  integerRootProduct_monic _

theorem endpointDenominator_degree (b : ℕ) :
    (endpointDenominator (K:=K) b).natDegree=2*b := by
  rw [endpointDenominator,integerRootProduct_degree,Int.card_Ico]
  omega

theorem centeredDenominator_endpoint_factor (b : ℕ) :
    centeredDenominator (K:=K) b=(X-C (b:K))*endpointDenominator b := by
  rw [centeredDenominator_integerProduct,poleWindow,
    ← Finset.Ico_insert_right (show -(b:ℤ)≤b by omega),integerRootProduct,Finset.prod_insert]
  · simp only [Int.cast_natCast]
    rfl
  · simp

theorem endpointDenominator_dvd {a b : ℕ} (hab : a≤b) :
    endpointDenominator (K:=K) a ∣ endpointDenominator b := by
  unfold endpointDenominator integerRootProduct
  apply Finset.prod_dvd_prod_of_subset _ _ _
  intro j hj
  simp only [Finset.mem_Ico] at hj ⊢
  omega

theorem endpointDenominator_eval_boundary (b : ℕ) :
    (endpointDenominator (K:=K) b).eval (b:K)≠0 := by
  intro hz
  obtain ⟨j,hj,heq⟩ := (integerRootProduct_eval_zero_iff _ _).mp hz
  have heqZ : (b:ℤ)=j := by exact_mod_cast heq
  simp only [Finset.mem_Ico] at hj
  omega

def endpointPadding (b a : ℕ) : K[X] := endpointDenominator b /ₘ endpointDenominator a

theorem endpointPadding_mul (a b : ℕ) (hab : a≤b) :
    endpointPadding (K:=K) b a * endpointDenominator a=endpointDenominator b := by
  have h := Polynomial.modByMonic_add_div (endpointDenominator (K:=K) b) (endpointDenominator a)
  rw [(Polynomial.modByMonic_eq_zero_iff_dvd (endpointDenominator_monic a)).mpr
    (endpointDenominator_dvd hab),zero_add] at h
  simpa only [endpointPadding,mul_comm] using h

theorem endpointPadding_ne_zero (a b : ℕ) (hab : a≤b) :
    endpointPadding (K:=K) b a≠0 := by
  intro hz
  have h := endpointPadding_mul (K:=K) a b hab
  rw [hz,zero_mul] at h
  exact (endpointDenominator_monic b).ne_zero h.symm

theorem endpointPadding_degree (a b : ℕ) (hab : a≤b) :
    (endpointPadding (K:=K) b a).natDegree=2*b-2*a := by
  have h := congrArg Polynomial.natDegree (endpointPadding_mul (K:=K) a b hab)
  rw [Polynomial.natDegree_mul (endpointPadding_ne_zero a b hab)
    (endpointDenominator_monic a).ne_zero,endpointDenominator_degree,endpointDenominator_degree] at h
  omega

end OddZeta.FourValue

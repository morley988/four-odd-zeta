import FourValueResidueSum
import FourValueTargetPearson

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem weightTestNumerator_residue_degree (b : ℕ) (a : Fin 15 → ℕ)
    (ha : ∀ i,a i≤b) (p : K[X]) (hp : (p.natDegree:ℤ)≤tupleBeta b a+3) :
    (weightTestNumerator b a p).natDegree < 20*b+9 := by
  have hpad := tupleWeightPadding_degree (K:=K) b a ha
  have hcomp := Polynomial.natDegree_comp_le (p:=p) (q:=(X^2:K[X]))
  have h₁ := Polynomial.natDegree_mul_le (p:=C 2*X*tupleWeightPadding (K:=K) b a) (q:=p.comp (X^2))
  have h₂ := Polynomial.natDegree_mul_le (p:=C (2:K)*X) (q:=tupleWeightPadding b a)
  have h₃ : (C (2:K)*X).natDegree=1 := by
    rw [Polynomial.natDegree_C_mul (by norm_num : (2:K)≠0),Polynomial.natDegree_X]
  rw [h₃] at h₂
  simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X] at hcomp
  unfold weightTestNumerator
  unfold tupleBeta at hp
  have hs : (∑ i,(a i:ℤ))=((∑ i,a i:ℕ):ℤ) := by simp
  rw [hs] at hp
  omega

theorem concreteB_one_zero (b : ℕ) (a : Fin 15 → ℕ) (ha : ∀ i,a i≤b)
    (p : K[X]) (hp : (p.natDegree:ℤ)≤tupleBeta b a+3) : concreteB b a 1 p=0 := by
  obtain ⟨c,hc⟩ := tupleRationalTest_partialFractions b a ha p hp
  rw [tupleRationalTest_padded b a ha p] at hc
  change rationalB b 1 (tupleRationalTest b a p)=0
  rw [tupleRationalTest_padded b a ha p,rationalB_one_coefficient b _ c hc]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (weightTestNumerator_residue_degree b a ha p hp)

theorem tupleWeightPadding_monic (b : ℕ) (a : Fin 15 → ℕ) (ha : ∀ i,a i≤b) :
    (tupleWeightPadding (K:=K) b a).Monic := by
  apply (tupleDenominator_monic a).of_mul_monic_right
  rw [tupleWeightPadding_product b a ha]
  exact (centeredDenominator_monic b).pow 15

theorem targetWeightPadding_degree (n : ℕ) :
    (tupleWeightPadding (K:=K) (100*n) (targetEndpointTuple n)).natDegree=1278*n := by
  have hd := tupleWeightPadding_degree (K:=K) (100*n) (targetEndpointTuple n)
    (targetEndpointTuple_bounded n)
  have hs : (∑ i,targetEndpointTuple n i)=861*n := by
    norm_num [targetEndpointTuple,Fin.sum_univ_succ]
    omega
  rw [hs] at hd
  omega

/-- A high-degree odd test detects the otherwise invisible total-residue solution. -/
theorem targetGrid_minus_one_detected (n : ℕ) :
    finiteGridFunctional (K:=K) (100*n) (targetEndpointTuple n) (-1)
      (X^(722*n+9)) = (2:K)^(722*n+10) := by
  let b := 100*n
  let a := targetEndpointTuple n
  let d := 722*n+9
  let p : K[X] := C ((2:K)^(d+1))*(tupleWeightPadding b a*X^d)
  have hm : (tupleWeightPadding (K:=K) b a*X^d).Monic :=
    (tupleWeightPadding_monic b a (targetEndpointTuple_bounded n)).mul (Polynomial.monic_X_pow d)
  have hc : (2:K)^(d+1)≠0 := pow_ne_zero _ (by norm_num)
  have hd : p.natDegree=20*b+9 := by
    rw [show p=C ((2:K)^(d+1))*(tupleWeightPadding b a*X^d) from rfl,
      Polynomial.natDegree_C_mul hc,
      (tupleWeightPadding_monic b a (targetEndpointTuple_bounded n)).natDegree_mul
        (Polynomial.monic_X_pow d),Polynomial.natDegree_X_pow,targetWeightPadding_degree]
    dsimp [b,d]
    omega
  have heq : tupleEvenWeight b a*algebraMap K[X] (RatFunc K) ((X^d).comp (C 2*X)) =
      algebraMap K[X] (RatFunc K) p /
        algebraMap K[X] (RatFunc K) ((centeredDenominator b)^10) := by
    rw [tupleEvenWeight_padded b a (targetEndpointTuple_bounded n)]
    dsimp [p]
    simp only [Polynomial.pow_comp,Polynomial.X_comp,map_mul,map_pow,mul_pow,pow_succ,
      RatFunc.algebraMap_C]
    ring
  have hproper : p.natDegree < (integerRootProduct (K:=K) (poleWindow b)^10).natDegree := by
    rw [← centeredDenominator_integerProduct,Polynomial.natDegree_pow,centeredDenominator_degree,hd]
    omega
  obtain ⟨c,hpf⟩ := integer_partialFractions (poleWindow b) 10 p hproper
  rw [← centeredDenominator_integerProduct] at hpf
  have hodd : (X^d:K[X]).comp (-X)=-(X^d) := by
    rw [Polynomial.pow_comp,Polynomial.X_comp]
    exact (show Odd d from ⟨361*n+4,by dsimp [d]; omega⟩).neg_pow X
  change finiteGridFunctional b a (-1) (X^d)=_
  rw [finiteGridFunctional_on_odd b a (-1) _ hodd]
  change rationalGrid b (-1) _ = _
  rw [heq,show rationalGrid (K:=K) b (-1)=rationalB b 1 from rfl,
    rationalB_one_coefficient b p c hpf,← hd]
  change p.leadingCoeff=_
  rw [show p=C ((2:K)^(d+1))*(tupleWeightPadding b a*X^d) from rfl,
    hm.leadingCoeff_C_mul]

theorem targetGrid_minus_one_ne_zero (n : ℕ) :
    finiteGridFunctional (K:=K) (100*n) (targetEndpointTuple n) (-1)≠0 := by
  intro hz
  have heq := targetGrid_minus_one_detected (K:=K) n
  rw [hz,LinearMap.zero_apply] at heq
  exact pow_ne_zero _ (by norm_num : (2:K)≠0) heq.symm

end OddZeta.FourValue

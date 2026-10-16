import FourValueConcretePearson

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem centeredDenominator_dvd {a b : ℕ} (hab : a≤b) :
    centeredDenominator (K:=K) a ∣ centeredDenominator b := by
  rw [centeredDenominator_integerProduct,centeredDenominator_integerProduct]
  unfold integerRootProduct
  apply Finset.prod_dvd_prod_of_subset _ _ _
  intro j hj
  simp only [poleWindow,Finset.mem_Icc] at hj ⊢
  omega

def weightPadding (b a : ℕ) : K[X] := centeredDenominator b /ₘ centeredDenominator a

theorem weightPadding_mul (a b : ℕ) (hab : a≤b) :
    weightPadding (K:=K) b a*centeredDenominator a=centeredDenominator b := by
  have h := Polynomial.modByMonic_add_div (centeredDenominator (K:=K) b) (centeredDenominator a)
  rw [(Polynomial.modByMonic_eq_zero_iff_dvd (centeredDenominator_monic a)).mpr
    (centeredDenominator_dvd hab),zero_add] at h
  simpa only [weightPadding,mul_comm] using h

theorem weightPadding_ne_zero (a b : ℕ) (hab : a≤b) : weightPadding (K:=K) b a≠0 := by
  intro hz
  have h := weightPadding_mul (K:=K) a b hab
  rw [hz,zero_mul] at h
  exact (centeredDenominator_monic b).ne_zero h.symm

theorem weightPadding_degree (a b : ℕ) (hab : a≤b) :
    (weightPadding (K:=K) b a).natDegree+2*a=2*b := by
  have h := congrArg Polynomial.natDegree (weightPadding_mul (K:=K) a b hab)
  rw [Polynomial.natDegree_mul (weightPadding_ne_zero a b hab)
    (centeredDenominator_monic a).ne_zero,centeredDenominator_degree,centeredDenominator_degree] at h
  omega

def tupleWeightPadding (b : ℕ) (a : Fin 15 → ℕ) : K[X] := ∏ i,weightPadding b (a i)

theorem tupleWeightPadding_product (b : ℕ) (a : Fin 15 → ℕ) (ha : ∀ i,a i≤b) :
    tupleWeightPadding (K:=K) b a*tupleDenominator a=(centeredDenominator b)^15 := by
  rw [tupleWeightPadding,tupleDenominator,← Finset.prod_mul_distrib]
  simp_rw [weightPadding_mul _ _ (ha _)]
  simp

theorem tupleWeightPadding_degree (b : ℕ) (a : Fin 15 → ℕ) (ha : ∀ i,a i≤b) :
    (tupleWeightPadding (K:=K) b a).natDegree+2*(∑ i,a i)=30*b := by
  rw [tupleWeightPadding,Polynomial.natDegree_prod _ _ (fun i _ => weightPadding_ne_zero (a i) b (ha i))]
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  simp_rw [weightPadding_degree _ _ (ha _)]
  simp
  omega

def weightTestNumerator (b : ℕ) (a : Fin 15 → ℕ) (p : K[X]) : K[X] :=
  C 2*X*tupleWeightPadding b a*p.comp (X^2)

theorem tupleRationalTest_padded (b : ℕ) (a : Fin 15 → ℕ) (ha : ∀ i,a i≤b) (p : K[X]) :
    tupleRationalTest b a p=algebraMap K[X] (RatFunc K) (weightTestNumerator b a p)/
      algebraMap K[X] (RatFunc K) ((centeredDenominator b)^10) := by
  have hD : algebraMap K[X] (RatFunc K) (tupleDenominator (K:=K) a)≠0 :=
    RatFunc.algebraMap_ne_zero (tupleDenominator_monic a).ne_zero
  have hR : algebraMap K[X] (RatFunc K) (centeredDenominator (K:=K) b)≠0 :=
    RatFunc.algebraMap_ne_zero (centeredDenominator_monic b).ne_zero
  have hpad := congrArg (algebraMap K[X] (RatFunc K)) (tupleWeightPadding_product (K:=K) b a ha)
  simp only [map_mul,map_pow] at hpad
  change tupleWeight b a*algebraMap K[X] (RatFunc K) (p.comp (X^2))=_
  rw [tupleWeight,tupleNumerator,weightTestNumerator]
  simp only [map_mul,map_pow,map_ofNat]
  field_simp
  linear_combination -(algebraMap K[X] (RatFunc K) X)*
    algebraMap K[X] (RatFunc K) (p.comp (X^2))*hpad

theorem weightTestNumerator_degree (b : ℕ) (a : Fin 15 → ℕ) (ha : ∀ i,a i≤b)
    (p : K[X]) (hp : (p.natDegree:ℤ)≤tupleBeta b a+3) :
    (weightTestNumerator b a p).natDegree < ((centeredDenominator (K:=K) b)^10).natDegree := by
  have hpad := tupleWeightPadding_degree (K:=K) b a ha
  have hcomp := Polynomial.natDegree_comp_le (p:=p) (q:=(X^2:K[X]))
  have h₁ := Polynomial.natDegree_mul_le (p:=C 2*X*tupleWeightPadding (K:=K) b a) (q:=p.comp (X^2))
  have h₂ := Polynomial.natDegree_mul_le (p:=C (2:K)*X) (q:=tupleWeightPadding b a)
  have h₃ : (C (2:K)*X).natDegree=1 := by
    rw [Polynomial.natDegree_C_mul (by norm_num : (2:K)≠0),Polynomial.natDegree_X]
  rw [h₃] at h₂
  simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X] at hcomp
  rw [Polynomial.natDegree_pow,centeredDenominator_degree]
  unfold weightTestNumerator
  unfold tupleBeta at hp
  have hs : (∑ i,(a i:ℤ))=((∑ i,a i:ℕ):ℤ) := by simp
  rw [hs] at hp
  omega

/-- Actual partial fractions of every test weight in the manuscript's
proper degree range; no pole locations or pole-order bounds are assumed. -/
theorem tupleRationalTest_partialFractions (b : ℕ) (a : Fin 15 → ℕ)
    (ha : ∀ i,a i≤b) (p : K[X]) (hp : (p.natDegree:ℤ)≤tupleBeta b a+3) :
    ∃ c : ℤ → Fin 10 → K,
      tupleRationalTest b a p=∑ j ∈ poleWindow b,∑ k : Fin 10,c j k • rationalPole (j:K) (k.val+1) := by
  rw [tupleRationalTest_padded b a ha p]
  have hdeg := weightTestNumerator_degree b a ha p hp
  rw [centeredDenominator_integerProduct] at hdeg ⊢
  exact integer_partialFractions _ _ _ hdeg

/-- Coefficient recovery identifies the expansion coefficients with the
Laurent coefficients used in the concrete B and C definitions. -/
theorem integer_partialFractions_coefficient (S : Finset ℤ) (m : ℕ) (c : ℤ → Fin m → K)
    (f : RatFunc K) (hf : f=∑ j ∈ S,∑ k : Fin m,c j k • rationalPole (j:K) (k.val+1))
    (j : ℤ) (hj : j∈S) (k : Fin m) :
    rationalCoefficientAt (j:K) (-((k.val+1:ℕ):ℤ)) f=c j k := by
  rw [hf]
  simp only [map_sum,map_smul,rationalCoefficientAt_integerPole _ _ _ _ (Nat.succ_pos _)]
  simp [smul_eq_mul,mul_ite,hj,Fin.val_inj]

end OddZeta.FourValue

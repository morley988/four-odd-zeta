import FourValueGridRestrictions

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def clearedPole (b : ℕ) (j : ℤ) (k : Fin 10) : K[X] :=
  (integerRootProduct ((poleWindow b).erase j))^10*(X-C (j:K))^(9-k.val)

theorem centeredDenominator_erase_factor (b : ℕ) (j : ℤ) (hj : j∈poleWindow b) :
    centeredDenominator (K:=K) b=(X-C (j:K))*integerRootProduct ((poleWindow b).erase j) := by
  rw [centeredDenominator_integerProduct,integerRootProduct]
  exact (Finset.mul_prod_erase _ _ hj).symm

theorem clearedPole_monic (b : ℕ) (j : ℤ) (k : Fin 10) :
    (clearedPole (K:=K) b j k).Monic :=
  ((integerRootProduct_monic _).pow 10).mul ((Polynomial.monic_X_sub_C _).pow _)

theorem clearedPole_degree (b : ℕ) (j : ℤ) (hj : j∈poleWindow b) (k : Fin 10) :
    (clearedPole (K:=K) b j k).natDegree=20*b+9-k.val := by
  rw [clearedPole,((integerRootProduct_monic (K:=K) _).pow 10).natDegree_mul
    ((Polynomial.monic_X_sub_C (j:K)).pow _),Polynomial.natDegree_pow,
    Polynomial.natDegree_pow,integerRootProduct_degree,Finset.card_erase_of_mem hj,
    poleWindow,Int.card_Icc,Polynomial.natDegree_X_sub_C]
  have hk := k.isLt
  omega

theorem clearedPole_coefficient (b : ℕ) (j : ℤ) (hj : j∈poleWindow b) (k : Fin 10) :
    (clearedPole (K:=K) b j k).coeff (20*b+9)=if k=0 then 1 else 0 := by
  by_cases hk : k=0
  · subst k
    rw [if_pos rfl]
    simpa [clearedPole_degree b j hj] using (clearedPole_monic (K:=K) b j 0).coeff_natDegree
  · rw [if_neg hk]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [clearedPole_degree b j hj k]
    have hkval : k.val≠0 := fun hz => hk (Fin.ext hz)
    have hp : 0<k.val := by omega
    omega

theorem denominator_mul_pole (b : ℕ) (j : ℤ) (hj : j∈poleWindow b) (k : Fin 10) :
    algebraMap K[X] (RatFunc K) ((centeredDenominator b)^10)*rationalPole (j:K) (k.val+1) =
      algebraMap K[X] (RatFunc K) (clearedPole b j k) := by
  rw [centeredDenominator_erase_factor b j hj,clearedPole]
  simp only [map_mul,map_pow,rationalPole]
  have hn := RatFunc.algebraMap_ne_zero (K:=K) (Polynomial.monic_X_sub_C (j:K)).ne_zero
  have hk : 9-k.val+(k.val+1)=10 := by have := k.isLt; omega
  rw [mul_pow,inv_pow]
  rw [← div_eq_mul_inv]
  apply (div_eq_iff (pow_ne_zero _ hn)).mpr
  rw [mul_assoc,← pow_add,hk]
  ring

theorem partialFractions_cleared (b : ℕ) (p : K[X]) (c : ℤ → Fin 10 → K)
    (hp : algebraMap K[X] (RatFunc K) p /
      algebraMap K[X] (RatFunc K) ((centeredDenominator b)^10) =
      ∑ j ∈ poleWindow b,∑ k : Fin 10,c j k • rationalPole (j:K) (k.val+1)) :
    p=∑ j ∈ poleWindow b,∑ k : Fin 10,c j k • clearedPole b j k := by
  have hn := RatFunc.algebraMap_ne_zero (K:=K)
    (pow_ne_zero 10 (centeredDenominator_monic (K:=K) b).ne_zero)
  apply RatFunc.algebraMap_injective K
  have heq := congrArg (fun v : RatFunc K =>
    algebraMap K[X] (RatFunc K) ((centeredDenominator b)^10)*v) hp
  rw [mul_div_cancel₀ _ hn] at heq
  rw [heq]
  simp only [Finset.mul_sum,map_sum,Polynomial.smul_eq_C_mul,map_mul,RatFunc.smul_eq_C_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_assoc,mul_comm _ (RatFunc.C (c j k)),mul_assoc,denominator_mul_pole b j hj k,
    RatFunc.algebraMap_C]

/-- The total simple-pole coefficient is the coefficient immediately below
the common denominator's degree. This is an algebraic residue-at-infinity identity. -/
theorem rationalB_one_coefficient (b : ℕ) (p : K[X]) (c : ℤ → Fin 10 → K)
    (hp : algebraMap K[X] (RatFunc K) p /
      algebraMap K[X] (RatFunc K) ((centeredDenominator b)^10) =
      ∑ j ∈ poleWindow b,∑ k : Fin 10,c j k • rationalPole (j:K) (k.val+1)) :
    rationalB b 1 (algebraMap K[X] (RatFunc K) p /
      algebraMap K[X] (RatFunc K) ((centeredDenominator b)^10)) = p.coeff (20*b+9) := by
  rw [hp,partialFractions_cleared b p c hp]
  simp only [map_sum,map_smul,Polynomial.finset_sum_coeff,Polynomial.coeff_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k _
  rw [rationalB_pole b j hj (k.val+1) 1 (by omega),clearedPole_coefficient b j hj k]
  congr 1
  by_cases hk : k=0
  · subst k; simp
  · have hkval : k.val≠0 := fun hz => hk (Fin.ext hz)
    rw [if_neg (by omega),if_neg hk]

end OddZeta.FourValue

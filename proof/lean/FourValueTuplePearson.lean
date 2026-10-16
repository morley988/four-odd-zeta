import FourValueEndpointTransfer
import Mathlib.Tactic

/-! The Pearson polynomial and invertible endpoint step for every
admissible intermediate tuple, rather than only the final endpoint list. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def tupleBeta (b : ℕ) (a : Fin 15 → ℕ) : ℤ := (∑ i, (a i:ℤ))-5*b

def tuplePearsonPolynomial (b : ℕ) (a : Fin 15 → ℕ) : K[X] :=
  (X+C (2*(b:K)+2))^5 * linearRootProduct (List.ofFn (fun i => 2*(a i:K)))

theorem tuplePearson_monic (b : ℕ) (a : Fin 15 → ℕ) :
    (tuplePearsonPolynomial (K:=K) b a).Monic :=
  ((Polynomial.monic_X_add_C _).pow 5).mul (linearRootProduct_monic _)

theorem tuplePearson_degree (b : ℕ) (a : Fin 15 → ℕ) :
    (tuplePearsonPolynomial (K:=K) b a).natDegree=20 := by
  rw [tuplePearsonPolynomial,
    ((Polynomial.monic_X_add_C _).pow 5).natDegree_mul (linearRootProduct_monic _),
    Polynomial.natDegree_pow_X_add_C,linearRootProduct_degree]
  simp

theorem tuplePearson_nextCoeff (b : ℕ) (a : Fin 15 → ℕ) :
    (tuplePearsonPolynomial (K:=K) b a).nextCoeff=10-2*(tupleBeta b a:K) := by
  rw [tuplePearsonPolynomial,
    ((Polynomial.monic_X_add_C _).pow 5).nextCoeff_mul (linearRootProduct_monic _),
    (Polynomial.monic_X_add_C _).nextCoeff_pow,Polynomial.nextCoeff_X_add_C,
    linearRootProduct_nextCoeff]
  simp only [List.sum_ofFn,tupleBeta,Int.cast_sub,Int.cast_sum,Int.cast_mul,
    Int.cast_ofNat,Int.cast_natCast,← Finset.mul_sum]
  ring

theorem tuplePearson_endpoint_root (b : ℕ) (a : Fin 15 → ℕ) (i : Fin 15) :
    (tuplePearsonPolynomial (K:=K) b a).eval (2*(a i:K))=0 := by
  simp only [tuplePearsonPolynomial,Polynomial.eval_mul]
  have hz : (linearRootProduct (List.ofFn (fun i => 2*(a i:K)))).eval (2*(a i:K))=0 := by
    rw [linearRootProduct,Polynomial.eval_list_prod]
    apply List.prod_eq_zero_iff.mpr
    apply List.mem_map.mpr
    refine ⟨X-C (2*(a i:K)),?_,by simp⟩
    exact List.mem_map.mpr ⟨2*(a i:K),List.mem_ofFn.mpr ⟨i,rfl⟩,rfl⟩
  rw [hz,mul_zero]

theorem tuplePearson_reflected_endpoint_nonzero (b : ℕ) (a : Fin 15 → ℕ)
    (i : Fin 15) (hi : 0<a i) (hib : a i≤b) :
    (tuplePearsonPolynomial (K:=K) b a).eval (-2*(a i:K))≠0 := by
  rw [tuplePearsonPolynomial,Polynomial.eval_mul]
  apply mul_ne_zero
  · simp only [Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
    apply pow_ne_zero
    have h : -2*(a i:ℤ)+(2*b+2)≠0 := by omega
    exact_mod_cast h
  · rw [linearRootProduct,Polynomial.eval_list_prod]
    apply List.prod_ne_zero
    intro ht
    obtain ⟨p,hp,hp0⟩ := List.mem_map.mp ht
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hp
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C] at hp0
    have h : -2*(a i:ℤ)-2*(a j:ℤ)≠0 := by omega
    have hK : -2*(a i:K)-2*(a j:K)≠0 := by exact_mod_cast h
    exact hK hp0

theorem tuplePearson_relation_endpoint_nonzero (b : ℕ) (a : Fin 15 → ℕ)
    (i : Fin 15) (hi : 0<a i) (hib : a i≤b) :
    (pearsonOperator (tuplePearsonPolynomial (K:=K) b a) 1).eval ((2*(a i:K))^2)≠0 := by
  have h := pearsonOperator_eval_identity (tuplePearsonPolynomial (K:=K) b a) 1 (2*(a i:K))
  have hr := tuplePearson_endpoint_root (K:=K) b a i
  have href := tuplePearson_reflected_endpoint_nonzero (K:=K) b a i hi hib
  simp only [Polynomial.eval_one,hr,zero_mul,mul_one,zero_sub] at h
  intro hz
  rw [hz,mul_zero] at h
  apply href
  simpa only [neg_mul] using neg_eq_zero.mp h.symm

theorem tuplePearson_endpoint_multiplier_bijective (b : ℕ) (a : Fin 15 → ℕ)
    (i : Fin 15) (hi : 0<a i) (hib : a i≤b) :
    Function.Bijective (quotientEndpointMap
      (pearsonOperator (tuplePearsonPolynomial (K:=K) b a) 1) ((2*(a i:K))^2)) :=
  quotientEndpointMap_bijective _ _ (tuplePearson_relation_endpoint_nonzero b a i hi hib)

theorem tuplePearson_monomial_top_coefficient (b : ℕ) (a : Fin 15 → ℕ) (k : ℕ) :
    (pearsonOperator (tuplePearsonPolynomial (K:=K) b a) (X^k)).coeff (k+9)=
      4*((k:K)-(tupleBeta b a:K)+5) := by
  let F : K[X] := tuplePearsonPolynomial b a * (X+C (1:K))^(2*k)
  have hdeg : F.natDegree=20+2*k := by
    dsimp [F]
    rw [(tuplePearson_monic b a).natDegree_mul ((Polynomial.monic_X_add_C _).pow _),
      tuplePearson_degree,Polynomial.natDegree_pow_X_add_C]
  have hn : F.nextCoeff=10-2*(tupleBeta b a:K)+2*(k:K) := by
    dsimp [F]
    rw [(tuplePearson_monic b a).nextCoeff_mul ((Polynomial.monic_X_add_C _).pow _),
      tuplePearson_nextCoeff,(Polynomial.monic_X_add_C _).nextCoeff_pow,
      Polynomial.nextCoeff_X_add_C]
    simp
  have hc : F.coeff (2*(k+9)+1)=F.nextCoeff := by
    rw [Polynomial.nextCoeff_of_natDegree_pos (by omega),hdeg]
    congr 1
    omega
  rw [pearsonOperator_apply,Polynomial.coeff_smul,oddCompress_coeff]
  have heq : tuplePearsonPolynomial b a * (X^k).comp ((X+1)^2)=F := by
    simp [F,Polynomial.pow_comp,← pow_mul]
  rw [heq,hc,hn]
  simp only [smul_eq_mul]
  ring

theorem tuplePearson_relation_degree (b : ℕ) (a : Fin 15 → ℕ)
    (hbeta : 6≤tupleBeta b a) :
    (pearsonOperator (tuplePearsonPolynomial (K:=K) b a) 1).natDegree=9 := by
  have htop : (pearsonOperator (tuplePearsonPolynomial (K:=K) b a) 1).coeff 9≠0 := by
    have h := tuplePearson_monomial_top_coefficient (K:=K) b a 0
    simp only [pow_zero,Nat.cast_zero,zero_add,zero_sub] at h
    rw [h]
    apply mul_ne_zero (by norm_num)
    have hz : -(tupleBeta b a)+5≠0 := by omega
    exact_mod_cast hz
  apply le_antisymm
  · simpa using pearsonOperator_degree (tuplePearsonPolynomial (K:=K) b a) 1
      (by rw [tuplePearson_degree])
  · exact Polynomial.le_natDegree_of_ne_zero htop

end OddZeta.FourValue

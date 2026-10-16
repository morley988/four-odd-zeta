import FourValueGridHarmonics
import FourValueGridRestrictions

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem rationalGrid_pole_C_identity (b h : ℕ) (t : ℤ) (ht : t∈poleWindow b)
    (k : Fin 10) :
    rationalGrid (K:=K) b h (rationalPole (t:K) (k.val+1)) +
      rationalC b h (rationalPole (t:K) (k.val+1)) +
      (-1:K)^h * rationalC b h (rationalReflect (rationalPole (t:K) (k.val+1)))=0 := by
  have hmt : -t∈poleWindow b := by
    simp only [poleWindow,Finset.mem_Icc] at ht ⊢
    omega
  rw [rationalGrid_pole b h t ht,rationalC_pole b h t ht k.val k.isLt,
    rationalReflect_pole,map_smul,smul_eq_mul]
  rw [show -(t:K)=((-t:ℤ):K) by simp,rationalC_pole b h (-t) hmt k.val k.isLt]
  rw [sub_neg_eq_add,show k.val+h+1=(k.val+1)+h by omega,pow_add]
  ring

theorem rationalGrid_C_identity (b h : ℕ) (f : RatFunc K) (c : ℤ → Fin 10 → K)
    (hf : f=∑ j ∈ poleWindow b,∑ k : Fin 10,c j k • rationalPole (j:K) (k.val+1)) :
    rationalGrid b h f + rationalC b h f + (-1:K)^h*rationalC b h (rationalReflect f)=0 := by
  let L : RatFunc K →ₗ[K] K := rationalGrid b h + rationalC b h +
    (-1:K)^h • (rationalC b h).comp rationalReflect.toLinearMap
  change L f=0
  rw [hf,map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro k _
  rw [map_smul]
  have hz : L (rationalPole (j:K) (k.val+1))=0 :=
    rationalGrid_pole_C_identity b h j hj k
  rw [hz,smul_zero]

theorem rationalGrid_odd_C (b h : ℕ) (hh : Odd h) (f : RatFunc K)
    (hodd : rationalReflect f = -f) (c : ℤ → Fin 10 → K)
    (hf : f=∑ j ∈ poleWindow b,∑ k : Fin 10,c j k • rationalPole (j:K) (k.val+1)) :
    rationalGrid b h f = -2*rationalC b h f := by
  have heq := rationalGrid_C_identity b h f c hf
  rw [hodd,map_neg,hh.neg_one_pow] at heq
  linear_combination heq

theorem finiteGridFunctional_positive_lift (b h : ℕ) (a : Fin 15 → ℕ)
    (ha : ∀ i,a i≤b) (hh : Odd h) (p : K[X])
    (hp : ((p.comp (C 4*X)).natDegree:ℤ)≤tupleBeta b a+3) :
    finiteGridFunctional b a h (X*p.comp (X^2)) =
      -4*concreteC b a h (p.comp (C 4*X)) := by
  obtain ⟨c,hc⟩ := tupleRationalTest_partialFractions b a ha (p.comp (C 4*X)) hp
  rw [finiteGridFunctional_lift,rationalGrid_odd_C b h hh _
    (tupleRationalTest_reflect b a _) c hc]
  change 2*(-2*rationalC b h _) = -4*rationalC b h _
  ring

end OddZeta.FourValue

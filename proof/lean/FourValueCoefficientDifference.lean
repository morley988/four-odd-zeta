import FourValuePoleTaylor
import FourValueHarmonicDifference

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem rationalCoefficientAt_integerPole (i j : ℤ) (k l : ℕ) (hl : 0<l) :
    rationalCoefficientAt (i:K) (-(l:ℤ)) (rationalPole (j:K) k)=
      if i=j then (if l=k then 1 else 0) else 0 := by
  by_cases hij : i=j
  · subst i
    simp [rationalCoefficientAt_pole_self]
  · rw [if_neg hij]
    exact rationalCoefficientAt_pole_other_neg (j:K) (i:K) k
      (by exact_mod_cast hij) (-(l:ℤ)) (by omega)

theorem rationalB_pole (b : ℕ) (j : ℤ) (hj : j∈poleWindow b) (k l : ℕ) (hl : 0<l) :
    rationalB (K:=K) b l (rationalPole (j:K) k)=if l=k then 1 else 0 := by
  simp only [rationalB,LinearMap.sum_apply,rationalCoefficientAt_integerPole _ _ _ _ hl]
  simp [hj]

theorem rationalC_pole (b h : ℕ) (j : ℤ) (hj : j∈poleWindow b) (k : ℕ) (hk : k<10) :
    rationalC (K:=K) b h (rationalPole (j:K) (k+1)) =
      -(-1:K)^h * ((Nat.choose (k+h) h:K)*finiteHarmonic ((b-j).toNat) (k+h+1)) := by
  simp only [rationalC,LinearMap.smul_apply,LinearMap.sum_apply,smul_eq_mul,
    rationalCoefficientAt_integerPole _ _ _ _ (Nat.succ_pos _)]
  simp [mul_ite,hj,hk]

theorem rationalPole_shift_neg_one (j : ℤ) (k : ℕ) :
    rationalShift (-1:K) (rationalPole (j:K) k)=rationalPole ((j+1:ℤ):K) k := by
  rw [rationalPole_shift]
  simp

theorem rationalB_pole_difference (b : ℕ) (j : ℤ)
    (hj : j∈Finset.Ico (-(b:ℤ)) b) (k l : ℕ) (hl : 0<l) :
    rationalB (K:=K) b l (rationalPole (j:K) k-rationalShift (-1) (rationalPole (j:K) k))=0 := by
  have hj₁ : j∈poleWindow b := by simp only [poleWindow,Finset.mem_Icc,Finset.mem_Ico] at *; omega
  have hj₂ : j+1∈poleWindow b := by simp only [poleWindow,Finset.mem_Icc,Finset.mem_Ico] at *; omega
  rw [map_sub,rationalPole_shift_neg_one,rationalB_pole b j hj₁ k l hl,
    rationalB_pole b (j+1) hj₂ k l hl,sub_self]

theorem rationalC_pole_difference (b h : ℕ) (j : ℤ)
    (hj : j∈Finset.Ico (-(b:ℤ)) b) (k : ℕ) (hk : k<10) :
    rationalC (K:=K) b h (rationalPole (j:K) (k+1)-
      rationalShift (-1) (rationalPole (j:K) (k+1))) =
      -rationalCoefficientAt (b:K) h (rationalPole (j:K) (k+1)) := by
  have hj₁ : j∈poleWindow b := by simp only [poleWindow,Finset.mem_Icc,Finset.mem_Ico] at *; omega
  have hj₂ : j+1∈poleWindow b := by simp only [poleWindow,Finset.mem_Icc,Finset.mem_Ico] at *; omega
  have hjb : j<(b:ℤ) := (Finset.mem_Ico.mp hj).2
  have hbj : (b:K)≠(j:K) := by
    intro heq
    have : (b:ℤ)=j := by exact_mod_cast heq
    omega
  rw [map_sub,rationalPole_shift_neg_one,rationalC_pole b h j hj₁ k hk,
    rationalC_pole b h (j+1) hj₂ k hk,rationalCoefficientAt_pole_regular _ _ hbj]
  rw [show -(-1:K)^h * ((Nat.choose (k+h) h:K)*finiteHarmonic ((b-j).toNat) (k+h+1))-
      -(-1:K)^h*((Nat.choose (k+h) h:K)*finiteHarmonic ((b-(j+1)).toNat) (k+h+1)) =
      -(-1:K)^h*(Nat.choose (k+h) h:K)*
      (finiteHarmonic ((b-j).toNat) (k+h+1)-finiteHarmonic ((b-(j+1)).toNat) (k+h+1)) by ring]
  rw [finiteHarmonic_boundary b j hjb]
  ring


def rationalDifference : RatFunc K →ₗ[K] RatFunc K :=
  LinearMap.id - (rationalShift (-1:K)).toLinearMap

theorem rationalDifference_apply (f : RatFunc K) :
    rationalDifference f=f-rationalShift (-1) f := rfl

theorem rationalB_difference_of_partialFractions (b l : ℕ) (hl : 0<l)
    (H : RatFunc K) (c : ℤ → Fin 10 → K)
    (hH : H=∑ j ∈ Finset.Ico (-(b:ℤ)) b,∑ k : Fin 10,c j k • rationalPole (j:K) (k.val+1)) :
    rationalB b l (rationalDifference H)=0 := by
  let L := (rationalB (K:=K) b l).comp rationalDifference
  change L H=0
  rw [hH,map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro k _
  rw [map_smul]
  have hz : L (rationalPole (j:K) (k.val+1))=0 :=
    rationalB_pole_difference b j hj (k.val+1) l hl
  rw [hz,smul_zero]

theorem rationalC_difference_of_partialFractions (b h : ℕ)
    (H : RatFunc K) (c : ℤ → Fin 10 → K)
    (hH : H=∑ j ∈ Finset.Ico (-(b:ℤ)) b,∑ k : Fin 10,c j k • rationalPole (j:K) (k.val+1)) :
    rationalC b h (rationalDifference H) = -rationalCoefficientAt (b:K) h H := by
  let L := (rationalC (K:=K) b h).comp rationalDifference + rationalCoefficientAt (b:K) h
  have hz : L H=0 := by
    rw [hH,map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [map_smul]
    have hz : L (rationalPole (j:K) (k.val+1))=0 := by
      change rationalC b h (rationalDifference (rationalPole (j:K) (k.val+1))) +
        rationalCoefficientAt (b:K) h (rationalPole (j:K) (k.val+1))=0
      rw [rationalDifference_apply,rationalC_pole_difference b h j hj k.val k.isLt,neg_add_cancel]
    rw [hz,smul_zero]
  exact eq_neg_of_add_eq_zero_left hz

end OddZeta.FourValue

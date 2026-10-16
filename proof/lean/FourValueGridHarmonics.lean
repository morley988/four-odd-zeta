import FourValueRationalReflection

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem integer_upper_harmonic (b : ℕ) (t : ℤ) (s : ℕ) :
    (∑ j ∈ Finset.Ioc t (b:ℤ), 1/((j:K)-(t:K))^s) =
      finiteHarmonic (K:=K) ((b-t).toNat) s := by
  unfold finiteHarmonic
  apply Finset.sum_bij (fun j _ => (j-t-1).toNat)
  · intro j hj
    simp only [Finset.mem_Ioc] at hj
    simp only [Finset.mem_range]
    omega
  · intro i hi j hj heq
    simp only [Finset.mem_Ioc] at hi hj
    omega
  · intro r hr
    simp only [Finset.mem_range] at hr
    refine ⟨t+(r:ℤ)+1,?_,?_⟩
    · simp only [Finset.mem_Ioc]; omega
    · omega
  · intro j hj
    have hc : (((j-t-1).toNat+1:ℕ):K)=(j:K)-(t:K) := by
      have hz : (((j-t-1).toNat+1:ℕ):ℤ)=j-t := by
        simp only [Finset.mem_Ioc] at hj
        omega
      exact_mod_cast hz
    rw [hc]

theorem integer_lower_harmonic (b : ℕ) (t : ℤ) (s : ℕ) :
    (∑ j ∈ Finset.Ico (-(b:ℤ)) t, 1/((j:K)-(t:K))^s) =
      (-1:K)^s * finiteHarmonic (K:=K) ((b+t).toNat) s := by
  rw [finiteHarmonic,Finset.mul_sum]
  apply Finset.sum_bij (fun j _ => (t-j-1).toNat)
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    simp only [Finset.mem_range]
    omega
  · intro i hi j hj heq
    simp only [Finset.mem_Ico] at hi hj
    omega
  · intro r hr
    simp only [Finset.mem_range] at hr
    refine ⟨t-(r:ℤ)-1,?_,?_⟩
    · simp only [Finset.mem_Ico]; omega
    · omega
  · intro j hj
    have hc : (((t-j-1).toNat+1:ℕ):K)=-((j:K)-(t:K)) := by
      have hz : (((t-j-1).toNat+1:ℕ):ℤ)=-(j-t) := by
        simp only [Finset.mem_Ico] at hj
        omega
      exact_mod_cast hz
    rw [hc,neg_pow ((j:K)-(t:K)) s,one_div,one_div,mul_inv_rev]
    rw [mul_left_comm,mul_inv_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)),mul_one]

theorem integer_window_split (b : ℕ) (t : ℤ) (ht : t∈poleWindow b) (f : ℤ → K) :
    (∑ j ∈ poleWindow b, f j) =
      (∑ j ∈ Finset.Ico (-(b:ℤ)) t, f j) + f t +
      ∑ j ∈ Finset.Ioc t (b:ℤ), f j := by
  have heq : poleWindow b = (Finset.Ico (-(b:ℤ)) t ∪ {t}) ∪ Finset.Ioc t (b:ℤ) := by
    ext j
    simp only [poleWindow,Finset.mem_Icc] at ht
    simp only [poleWindow,Finset.mem_Icc,Finset.mem_union,Finset.mem_Ico,
      Finset.mem_singleton,Finset.mem_Ioc]
    omega
  have hd₁ : Disjoint (Finset.Ico (-(b:ℤ)) t) ({t}:Finset ℤ) := by simp
  have hd₂ : Disjoint (Finset.Ico (-(b:ℤ)) t ∪ {t}) (Finset.Ioc t (b:ℤ)) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    simp only [Finset.mem_union,Finset.mem_Ico,Finset.mem_singleton,Finset.mem_Ioc] at hj hk
    omega
  rw [heq,Finset.sum_union hd₂,Finset.sum_union hd₁,Finset.sum_singleton]

theorem rationalGrid_pole (b h : ℕ) (t : ℤ) (ht : t∈poleWindow b) (k : ℕ) :
    rationalGrid (K:=K) b h (rationalPole (t:K) (k+1)) =
      (-1:K)^h * (Nat.choose (k+h) h:K) *
        (finiteHarmonic ((b-t).toNat) (k+h+1) +
          (-1:K)^(k+h+1)*finiteHarmonic ((b+t).toNat) (k+h+1)) := by
  simp only [rationalGrid,LinearMap.sum_apply]
  rw [integer_window_split b t ht]
  have hm : rationalCoefficientAt (t:K) h (rationalPole (t:K) (k+1))=0 := by
    rw [rationalCoefficientAt_pole_self,if_neg (by omega)]
  rw [hm,add_zero]
  have hl : (∑ j ∈ Finset.Ico (-(b:ℤ)) t,
      rationalCoefficientAt (j:K) h (rationalPole (t:K) (k+1))) =
      (-1:K)^h*(Nat.choose (k+h) h:K)*
        ((-1:K)^(k+h+1)*finiteHarmonic ((b+t).toNat) (k+h+1)) := by
    rw [← integer_lower_harmonic,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [rationalCoefficientAt_pole_regular (t:K) (j:K)
      (by exact_mod_cast (ne_of_lt (Finset.mem_Ico.mp hj).2))]
    ring
  have hr : (∑ j ∈ Finset.Ioc t (b:ℤ),
      rationalCoefficientAt (j:K) h (rationalPole (t:K) (k+1))) =
      (-1:K)^h*(Nat.choose (k+h) h:K)*finiteHarmonic ((b-t).toNat) (k+h+1) := by
    rw [← integer_upper_harmonic,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [rationalCoefficientAt_pole_regular (t:K) (j:K)
      (by exact_mod_cast (ne_of_gt (Finset.mem_Ioc.mp hj).1))]
    ring
  rw [hl,hr]
  ring

end OddZeta.FourValue

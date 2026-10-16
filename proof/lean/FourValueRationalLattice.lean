import FourValueRationalBoxes
import Mathlib.Data.Int.Interval

namespace OddZeta.FourValue.RationalBoxes
open Finset

theorem integer_interval_count (S : Finset ℤ) (a b : ℚ) (hab : a≤b)
 (hS : ∀z∈S,a≤(z:ℚ) ∧ (z:ℚ)≤b) : (S.card:ℚ)≤b-a+1 := by
 have hsub : S⊆Icc ⌈a⌉ ⌊b⌋ := by
   intro z hz
   exact mem_Icc.mpr ⟨Int.ceil_le.mpr (hS z hz).1,Int.le_floor.mpr (hS z hz).2⟩
 have hc := card_le_card hsub
 have ha := Int.le_ceil a
 have hb := Int.floor_le b
 by_cases he : ⌈a⌉≤⌊b⌋+1
 · have hcard := Int.card_Icc_of_le ⌈a⌉ ⌊b⌋ he
   have hcardR : ((Icc ⌈a⌉ ⌊b⌋).card:ℚ)=(⌊b⌋:ℚ)+1-(⌈a⌉:ℚ) := by exact_mod_cast hcard
   have hcR : (S.card:ℚ)≤((Icc ⌈a⌉ ⌊b⌋).card:ℚ) := by exact_mod_cast hc
   linarith
 · have hz : (Icc ⌈a⌉ ⌊b⌋).card=0 := by rw [Int.card_Icc]; omega
   have : S.card=0 := by omega
   rw [this,Nat.cast_zero]
   linarith

/-- One uniform lattice-point error per box, independent of n. -/
theorem scaled_integer_interval_count (S : Finset ℤ) (a b N : ℚ)
 (hN : 0<N) (hab : a≤b)
 (hS : ∀z∈S,a≤(z:ℚ)/N ∧ (z:ℚ)/N≤b) :
 (S.card:ℚ)≤N*(b-a)+1 := by
 have h := integer_interval_count S (a*N) (b*N)
   (mul_le_mul_of_nonneg_right hab hN.le)
   (fun z hz => ⟨(le_div_iff₀ hN).mp (hS z hz).1,(div_le_iff₀ hN).mp (hS z hz).2⟩)
 nlinarith

/-- A finite partition's rounding errors add only a constant penalty. -/
theorem weighted_count_upper {ι : Type*} [Fintype ι]
 (counts : ι → ℕ) (width pen : ι → ℚ) (N : ℚ)
 (hp : ∀i,0≤pen i) (hc : ∀i,(counts i:ℚ)≤N*width i+1) :
 (∑i,(counts i:ℚ)*pen i) ≤ N*(∑i,width i*pen i)+∑i,pen i := by
 have h := sum_le_sum (s:=univ) (fun i _ => mul_le_mul_of_nonneg_right (hc i) (hp i))
 simpa only [add_mul,one_mul,mul_assoc,sum_add_distrib,mul_sum] using h

#print axioms scaled_integer_interval_count
#print axioms weighted_count_upper
end OddZeta.FourValue.RationalBoxes

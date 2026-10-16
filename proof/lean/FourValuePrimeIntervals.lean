import FourValuePrimeAsymptotic

noncomputable section
namespace OddZeta.FourValue.PrimeAsymptotic
open Finset
open scoped Chebyshev

theorem theta_filter (N : ℕ) (x : ℝ) (hx : 0≤x) (hN : x≤N) :
 (∑p∈Nat.primesLE N,if (p:ℝ)≤x then Real.log p else 0)=θ x := by
 rw [← sum_filter,Chebyshev.theta_eq_sum_primesLE]
 congr 1
 ext p
 simp only [mem_filter,Nat.mem_primesLE]
 have hf : p≤⌊x⌋₊ ↔ (p:ℝ)≤x := Nat.le_floor_iff hx
 constructor
 · intro hh
   exact ⟨hf.mpr hh.2,hh.1.2⟩
 · intro hh
   have hp := hf.mp hh.1
   exact ⟨⟨by exact_mod_cast hp.trans hN,hh.2⟩,hp⟩

theorem theta_interval_sum (N : ℕ) (a b : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤N) :
 (∑p∈Nat.primesLE N,if a<(p:ℝ) ∧ (p:ℝ)≤b then Real.log p else 0)=θ b-θ a := by
 rw [← theta_filter N b (ha.trans hab) hb,← theta_filter N a ha (hab.trans hb),← sum_sub_distrib]
 apply sum_congr rfl
 intro p hp
 by_cases h1 : (p:ℝ)≤a <;> by_cases h2 : (p:ℝ)≤b
 · simp [h1,h2,not_lt_of_ge h1]
 · have := h1.trans hab; contradiction
 · simp [h1,h2,lt_of_not_ge h1]
 · simp [h1,h2]

end OddZeta.FourValue.PrimeAsymptotic

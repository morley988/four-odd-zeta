import FourValuePrimeAsymptotic

noncomputable section
namespace OddZeta.FourValue.PrimeAsymptotic
open Finset
open scoped Chebyshev

/-- Bound the omitted primes without losing a second linear prime contribution. -/
theorem truncated_log_sum_le (T X : ℕ) (hTX : T≤X) :
 (∑p∈Nat.primesLE T,(Nat.log p X:ℝ)*Real.log p) ≤ ψ (X:ℝ)-θ (X:ℝ)+θ (T:ℝ) := by
 have hsub : Nat.primesLE T ⊆ Nat.primesLE X := by
   intro p hp
   simp only [Nat.mem_primesLE] at hp ⊢
   exact ⟨hp.1.trans hTX,hp.2⟩
 have he (N : ℕ) :
   (∑p∈Nat.primesLE N,((Nat.log p X:ℝ)-1)*Real.log p)=
   (∑p∈Nat.primesLE N,(Nat.log p X:ℝ)*Real.log p)-θ (N:ℝ) := by
   rw [Chebyshev.theta_eq_sum_primesLE_log,← sum_sub_distrib]
   apply sum_congr rfl
   intro p hp
   ring
 have hsum : (∑p∈Nat.primesLE T,((Nat.log p X:ℝ)-1)*Real.log p) ≤
   ∑p∈Nat.primesLE X,((Nat.log p X:ℝ)-1)*Real.log p := by
   apply sum_le_sum_of_subset_of_nonneg hsub
   intro p hp hn
   obtain ⟨hpX,hpr⟩ := Nat.mem_primesLE.mp hp
   have hlog : (1:ℝ)≤Nat.log p X := by
     exact_mod_cast Nat.log_pos hpr.one_lt hpX
   exact mul_nonneg (sub_nonneg.mpr hlog)
     (Real.log_nonneg (by exact_mod_cast hpr.one_le))
 rw [he T,he X,← Chebyshev.psi_eq_sum_mul_log_prime] at hsum
 linarith

#print axioms truncated_log_sum_le
end OddZeta.FourValue.PrimeAsymptotic

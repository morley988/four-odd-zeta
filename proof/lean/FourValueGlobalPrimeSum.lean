import FourValueGlobalPrimePoint
import FourValueGlobalProduct
import FourValuePrimeIntervals
import FourValueSmallPrimeSum
import FourValueGlobalRates

noncomputable section
namespace OddZeta.FourValue.ArithmeticCertificate
open Corrected Finset
open scoped Chebyshev

def Grid.primeSum (G : Grid) (n : ℕ) : ℝ :=
 ∑i,((G.cell i).lower:ℝ)*(θ (((G.cell i).hi:ℝ)*n)-θ (((G.cell i).lo:ℝ)*n))
def Grid.logBound (G : Grid) (n Q : ℕ) : ℝ :=
 (n:ℝ)*G.primeSum n-(G.error:ℝ)*θ (361*(n:ℝ))-smallPrimeEnvelope n-
 (analyticMinorSize n:ℝ)*Real.log Q

theorem Grid.step_prime_sum (G : Grid) (hG : G.Valid) (n : ℕ) (hn : 0<n) :
 (∑p∈Nat.primesLE (361*n),(G.step ((p:ℚ)/n):ℝ)*Real.log p)=G.primeSum n := by
 have hnR : (0:ℝ)<n := by exact_mod_cast hn
 have hnQ : (0:ℚ)<n := by exact_mod_cast hn
 unfold Grid.step Grid.primeSum
 simp only [Rat.cast_sum,apply_ite,Rat.cast_zero,sum_mul]
 rw [sum_comm]
 apply sum_congr rfl
 intro i _
 have hc := (hG.cells i).2.2
 have he (p : ℕ) : ((G.cell i).lo<(p:ℚ)/n ∧ (p:ℚ)/n≤(G.cell i).hi) ↔
   ((G.cell i).lo:ℝ)*n<(p:ℝ) ∧ (p:ℝ)≤((G.cell i).hi:ℝ)*n := by
   rw [lt_div_iff₀ hnQ,div_le_iff₀ hnQ]
   constructor <;> intro hh <;> exact_mod_cast hh
 simp_rw [he,ite_mul,zero_mul]
 have ha : (0:ℝ)≤((G.cell i).lo:ℝ)*n := by
   have hh : (0:ℚ)≤(G.cell i).lo := le_trans (by norm_num) hc.lo_pos
   positivity
 have hab : ((G.cell i).lo:ℝ)*n≤((G.cell i).hi:ℝ)*n :=
   mul_le_mul_of_nonneg_right (by exact_mod_cast hc.lt.le) hnR.le
 have hb : ((G.cell i).hi:ℝ)*n≤(361*n:ℕ) := by
   push_cast
   exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc.hi_le) hnR.le
 rw [← PrimeAsymptotic.theta_interval_sum (361*n) _ _ ha hab hb,mul_sum]
 apply sum_congr rfl
 intro p hp
 split_ifs <;> simp

theorem small_prime_log_sum (n : ℕ) :
 (∑p∈Nat.primesLE (361*n),(if p≤n/20 then (Nat.log p (800*n):ℝ) else 0)*Real.log p)≤
 ψ (800*(n:ℝ))-θ (800*(n:ℝ))+θ ((n:ℝ)/20) := by
 have he : (Nat.primesLE (361*n)).filter (fun p => p≤n/20)=Nat.primesLE (n/20) := by
   ext p
   simp only [mem_filter,Nat.mem_primesLE]
   constructor
   · rintro ⟨⟨_,hprime⟩,hsmall⟩
     exact ⟨hsmall,hprime⟩
   · rintro ⟨hsmall,hprime⟩
     exact ⟨⟨by omega,hprime⟩,hsmall⟩
 simp only [ite_mul,zero_mul,← sum_filter,he]
 have hh := PrimeAsymptotic.truncated_log_sum_le (n/20) (800*n) (by omega)
 have hm : θ (n/20:ℕ)≤θ ((n:ℝ)/20) := by
   apply Chebyshev.theta_mono
   have hh := Nat.div_mul_le_self n 20
   have hhR : ((n/20:ℕ):ℝ)*20≤n := by exact_mod_cast hh
   linarith
 push_cast at hh
 linarith

theorem nat_valuation_prime_sum (Q N : ℕ) (hQ : 0<Q) :
 (∑p∈Nat.primesLE N,(padicValNat p Q:ℝ)*Real.log p)≤Real.log Q := by
 have hh := ProductFormula.finite_prime_lower (Q:ℚ) (by exact_mod_cast hQ.ne')
   (Nat.primesLE N) (fun p => (padicValNat p Q:ℝ))
   (fun p hp => (Nat.mem_primesLE.mp hp).2)
   (fun p _ => by simp [padicValRat.of_nat])
   (fun p _ _ => by simp [padicValRat.of_nat])
 simpa using hh

theorem Grid.log_bound (G : Grid) (hG : G.Valid) (n : ℕ) (z : Fin 4 → ℚ)
 (hn : 320000≤n) (hQ : 20*rationalPencilDenominator z≤n)
 (rows cols : Fin (analyticMinorSize n) ↪ Fin (targetHankelDegree n+1))
 (hq : ((Corrected.rationalFourValueMatrix n z).submatrix rows cols).det≠0) :
 G.logBound n (rationalPencilDenominator z)≤
 Real.log |(((Corrected.rationalFourValueMatrix n z).submatrix rows cols).det:ℝ)| := by
 let q := ((Corrected.rationalFourValueMatrix n z).submatrix rows cols).det
 let Q := rationalPencilDenominator z
 let w : ℕ → ℝ := fun p => (n:ℝ)*(G.step ((p:ℚ)/n):ℝ)-(G.error:ℝ)-
   40*(analyticMinorSize n:ℝ)*(if p≤n/20 then (Nat.log p (800*n):ℝ) else 0)-
   (analyticMinorSize n:ℝ)*padicValNat p Q
 have hh := ProductFormula.finite_prime_lower q hq (Nat.primesLE (361*n)) w
   (fun p hp => (Nat.mem_primesLE.mp hp).2) (by
     intro p hp
     obtain ⟨hpN,hprime⟩ := Nat.mem_primesLE.mp hp
     letI : Fact p.Prime := ⟨hprime⟩
     have hv := G.prime_lower hG n z hn hQ rows cols hq hpN
     dsimp [w,q,Q]
     have hr := (Rat.cast_le (K:=ℝ)).mpr hv
     simpa only [Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,Rat.cast_intCast,
       Rat.cast_ofNat,apply_ite,Rat.cast_zero] using hr) (by
     intro p hp hpN
     letI : Fact p.Prime := ⟨hp⟩
     have hlarge : 361*n<p := by
       by_contra hh
       exact hpN (Nat.mem_primesLE.mpr ⟨by omega,hp⟩)
     exact G.prime_tail n z hn hQ rows cols hq hlarge)
 have hs := G.step_prime_sum hG n (by omega)
 have hsmall := small_prime_log_sum n
 have hden := nat_valuation_prime_sum Q (361*n) (rationalPencilDenominator_pos z)
 have he : (∑p∈Nat.primesLE (361*n),w p*Real.log p)=
 (n:ℝ)*G.primeSum n-(G.error:ℝ)*θ (361*(n:ℝ))-
 40*(analyticMinorSize n:ℝ)*(∑p∈Nat.primesLE (361*n),(if p≤n/20 then (Nat.log p (800*n):ℝ) else 0)*Real.log p)-
 (analyticMinorSize n:ℝ)*(∑p∈Nat.primesLE (361*n),(padicValNat p Q:ℝ)*Real.log p) := by
   simp only [w,sub_mul,mul_assoc,sum_sub_distrib,← mul_sum,hs]
   rw [← Chebyshev.theta_eq_sum_primesLE_log]
   push_cast
   rfl
 rw [he] at hh
 have hkm : (0:ℝ)≤analyticMinorSize n := by positivity
 have hsm := mul_le_mul_of_nonneg_left hsmall (show (0:ℝ)≤40*analyticMinorSize n by positivity)
 have hdn := mul_le_mul_of_nonneg_left hden hkm
 unfold Grid.logBound smallPrimeEnvelope
 dsimp [q,Q] at hh hdn
 linarith
end OddZeta.FourValue.ArithmeticCertificate

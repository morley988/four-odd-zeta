import FourValueBoxSemantics

noncomputable section
namespace OddZeta.FourValue.ArithmeticCertificate
open Finset

theorem Cell.normalization_lower (c : Cell) (hv : c.Valid) (n p : ℕ)
 (hn : 0<n) (hx : c.lo<(p:ℚ)/n ∧ (p:ℚ)/n≤c.hi) :
 c.norm≤targetNormalizationFloor p n := by
 have hnq : (0:ℚ)<n := by exact_mod_cast hn
 have hpq : (0:ℚ)<p := by
   have hh : (0:ℚ)<(p:ℚ)/n := lt_of_lt_of_le (by norm_num) (hv.lo_pos.trans hx.1.le)
   exact (div_pos_iff.mp hh).elim (fun h => h.1) (fun h => False.elim (not_lt_of_ge hnq.le h.2))
 have hpz : (0:ℤ)<p := by exact_mod_cast hpq
 have hlow (i : Fin 10) : c.normFloors i≤(2*targetFactorialEndpoints i*n/p:ℕ) := by
   have hi := hv.normalization i
   have hmul := (mul_le_mul_of_nonneg_left hx.2 (show (0:ℚ)≤c.normFloors i by exact_mod_cast hi.1)).trans hi.2
   have hmul' : (c.normFloors i:ℚ)*(p:ℚ)≤2*(tailA i:ℚ)*n := by
     have hh := (div_le_iff₀ hnq).mp (show (c.normFloors i:ℚ)*p/n≤2*(tailA i:ℚ) by simpa [mul_div_assoc] using hmul)
     exact hh
   have ht : tailA i=targetFactorialEndpoints i := by fin_cases i <;> rfl
   rw [ht] at hmul'
   have hiZ : c.normFloors i*(p:ℤ)≤2*(targetFactorialEndpoints i:ℤ)*n := by exact_mod_cast hmul'
   have hh := (Int.le_ediv_iff_mul_le hpz).mpr hiZ
   simpa only [Int.natCast_ediv,Nat.cast_mul,Nat.cast_ofNat] using hh
 have hupper : (33*n/p:ℕ)≤c.norm33 := by
   have hj : (0:ℚ)<c.norm33+1 := by exact_mod_cast hv.norm33_pos
   have hh : (33:ℚ)<(c.norm33+1:ℚ)*(p:ℚ)/n := by
     have h := mul_lt_mul_of_pos_left hx.1 hj
     rw [← mul_div_assoc] at h
     exact hv.norm33_bound.trans_lt h
   have hh' := (lt_div_iff₀ hnq).mp hh
   have hz : 33*(n:ℤ)<(c.norm33+1)*(p:ℤ) := by exact_mod_cast hh'
   have hd := (Int.ediv_lt_iff_lt_mul hpz).mpr hz
   have hle : (33*(n:ℤ))/(p:ℤ)≤c.norm33 := by omega
   simpa only [Int.natCast_ediv,Nat.cast_mul,Nat.cast_ofNat] using hle
 unfold Cell.norm targetNormalizationFloor
 have hh := sum_le_sum (s:=univ) (fun i _ => hlow i)
 linarith
end OddZeta.FourValue.ArithmeticCertificate

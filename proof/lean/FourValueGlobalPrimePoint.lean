import FourValueArithmeticGrid
import FourValueGlobalTail

noncomputable section
namespace OddZeta.FourValue.ArithmeticCertificate
open Corrected Finset
variable {p : ℕ} [Fact p.Prime]

theorem Grid.error_nonneg (G : Grid) : 0≤G.error := by
 unfold Grid.error
 positivity

theorem large_prime_conditions (n Q : ℕ) (hn : 320000≤n) (hQ : 20*Q≤n)
 (hQpos : 0<Q) (hp : n/20<p) : 800*n<p^2 ∧ ¬p∣Q := by
 have h20 : n<20*p := by omega
 constructor
 · have hmul := Nat.mul_le_mul_right p (show 16000≤p by omega)
   nlinarith
 · intro hd
   have hle := Nat.le_of_dvd hQpos hd
   omega

theorem Grid.prime_lower (G : Grid) (hG : G.Valid) (n : ℕ) (z : Fin 4 → ℚ)
 (hn : 320000≤n) (hQ : 20*rationalPencilDenominator z≤n)
 (rows cols : Fin (analyticMinorSize n) ↪ Fin (targetHankelDegree n+1))
 (hq : ((Corrected.rationalFourValueMatrix n z).submatrix rows cols).det≠0) (hpN : p≤361*n) :
 (n:ℚ)*G.step ((p:ℚ)/n)-G.error-
 40*(analyticMinorSize n:ℚ)*(if p≤n/20 then (Nat.log p (800*n):ℚ) else 0)-
 (analyticMinorSize n:ℚ)*padicValNat p (rationalPencilDenominator z)≤
 (padicValRat p ((Corrected.rationalFourValueMatrix n z).submatrix rows cols).det:ℚ) := by
 have hnq : (0:ℚ)<n := by exact_mod_cast (show 0<n by omega)
 by_cases hsmall : p≤n/20
 · have hu : (p:ℚ)/n≤1/20 := by
     apply (div_le_iff₀ hnq).mpr
     have h : 20*p≤n := by omega
     have hh : (20:ℚ)*p≤n := by exact_mod_cast h
     linarith
   rw [G.step_zero_small hG _ hu,if_pos hsmall]
   have hv := (Corrected.rationalFourValueMatrix_allPrime_minor (p:=p) n z rows cols).of_ne_zero hq
   have hvq : (analyticMinorSize n:ℚ)*(-40*(Nat.log p (800*n):ℚ)-
     padicValNat p (rationalPencilDenominator z))≤
     (padicValRat p ((Corrected.rationalFourValueMatrix n z).submatrix rows cols).det:ℚ) := by
     have hh := (Int.cast_le (R:=ℚ)).mpr hv
     norm_num only [Int.cast_mul,Int.cast_sub,Int.cast_natCast,Int.cast_neg,Int.cast_ofNat,Int.cast_negSucc] at hh
     exact hh
   nlinarith [G.error_nonneg]
 · have hlarge : n/20<p := by omega
   have hh := large_prime_conditions (p:=p) n (rationalPencilDenominator z) hn hQ
     (rationalPencilDenominator_pos z) hlarge
   have hu : (1:ℚ)/20<(p:ℚ)/n ∧ (p:ℚ)/n≤361 := by
     constructor
     · apply (lt_div_iff₀ hnq).mpr
       have h : n<20*p := by omega
       have hh : (n:ℚ)<20*p := by exact_mod_cast h
       linarith
     · apply (div_le_iff₀ hnq).mpr
       exact_mod_cast hpN
   obtain ⟨i,hi⟩ := G.cover hG _ hu
   rw [G.step_eq hG _ i hi,if_neg hsmall]
   have hv := (G.cell i).valuation_lower (hG.cells i).2.2 n z (by omega) hi hh.1 hh.2 rows cols hq
   have he := G.error_ge i
   have hnon : (0:ℚ)≤(analyticMinorSize n:ℚ)*padicValNat p (rationalPencilDenominator z) := by positivity
   nlinarith

theorem Grid.prime_tail (G : Grid) (n : ℕ) (z : Fin 4 → ℚ)
 (hn : 320000≤n) (hQ : 20*rationalPencilDenominator z≤n)
 (rows cols : Fin (analyticMinorSize n) ↪ Fin (targetHankelDegree n+1))
 (hq : ((Corrected.rationalFourValueMatrix n z).submatrix rows cols).det≠0) (hpN : 361*n<p) :
 0≤padicValRat p ((Corrected.rationalFourValueMatrix n z).submatrix rows cols).det := by
 have hh := large_prime_conditions (p:=p) n (rationalPencilDenominator z) hn hQ
   (rationalPencilDenominator_pos z) (by omega)
 exact (rationalFourValueMatrix_integral_large n z rows cols hh.1 hh.2 hpN).of_ne_zero hq
end OddZeta.FourValue.ArithmeticCertificate

import FourValueFactorialStaircase
import FourValueCorrectedRate

noncomputable section
namespace OddZeta.FourValue.ArithmeticCertificate
open Finset Corrected
variable {p : ℕ} [Fact p.Prime]

theorem minor_size_error (n : ℕ) (hn : 0<n) :
 |(analyticMinorSize n:ℚ)-(361/2)*(n:ℚ)|≤4 := by
 have hd : 4≤targetHankelDegree n+1 := by unfold targetHankelDegree; omega
 have hk : analyticMinorSize n+4=targetHankelDegree n+1 := Nat.sub_add_cancel hd
 have ha:=Nat.div_mul_le_self (361*n) 2
 have hb:=Nat.lt_div_mul_add (a:=361*n) (by norm_num:0<2)
 have hkq : (analyticMinorSize n:ℚ)+4=targetHankelDegree n+1 := by exact_mod_cast hk
 have haq : (targetHankelDegree n:ℚ)*2≤361*n := by exact_mod_cast ha
 have hbq : (361:ℚ)*n<targetHankelDegree n*2+2 := by exact_mod_cast hb
 exact abs_le.mpr ⟨by linarith,by linarith⟩

def Cell.error (c : Cell) : ℚ := c.roundingPenalty+4*|c.price|+2*c.k

theorem Cell.valuation_lower (c : Cell) (hc : c.Valid) (n : ℕ) (z : Fin 4 → ℚ)
 (hn : 0<n) (hx : c.lo<(p:ℚ)/n ∧ (p:ℚ)/n≤c.hi)
 (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator z)
 (rows cols : Fin (analyticMinorSize n) ↪ Fin (targetHankelDegree n+1))
 (hq : ((Corrected.rationalFourValueMatrix n z).submatrix rows cols).det≠0) :
 (n:ℚ)*c.lower-c.error≤
 (padicValRat p ((Corrected.rationalFourValueMatrix n z).submatrix rows cols).det:ℚ) := by
 have hh := rationalFourValueMatrix_dual_bound n z rows cols c.price (c.classPenalty n)
   (fun r => c.local_minorLower hc n z hn hx hs hp r _)
 have hv : c.price*(analyticMinorSize n:ℤ)-∑r,c.classPenalty n r-
   selectedFactorialCost p n rows cols≤padicValRat p ((Corrected.rationalFourValueMatrix n z).submatrix rows cols).det := hh.resolve_left hq
 have hvq : (c.price:ℚ)*analyticMinorSize n-(∑r : Fin (p/2+1),(c.classPenalty n r:ℚ))-
   (selectedFactorialCost p n rows cols:ℚ)≤(padicValRat p ((Corrected.rationalFourValueMatrix n z).submatrix rows cols).det:ℚ) := by exact_mod_cast hv
 have hpens := c.penalty_sum_upper hc n p hn
 have hf := selected_factorial_upper n c.lo c.k hn (lt_of_lt_of_le (by norm_num) hc.lo_pos) hx.1 hc.k_bounds hs rows cols
 have he := minor_size_error n hn
 have hprice : (n:ℚ)*(361/2)*c.price-4*|(c.price:ℚ)|≤(c.price:ℚ)*analyticMinorSize n := by
   have ha := abs_mul (c.price:ℚ) ((analyticMinorSize n:ℚ)-(361/2)*n)
   have hb := mul_le_mul_of_nonneg_left he (abs_nonneg (c.price:ℚ))
   rw [← ha] at hb
   have hh := (abs_le.mp hb).1
   nlinarith
 have hlo := mul_le_mul_of_nonneg_left hc.lower_bound (show (0:ℚ)≤n by positivity)
 unfold Cell.error
 push_cast
 nlinarith
end OddZeta.FourValue.ArithmeticCertificate

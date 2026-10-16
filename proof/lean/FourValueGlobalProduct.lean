import FourValueProductFormula
import FourValuePadicMinors

noncomputable section
namespace OddZeta.FourValue.ProductFormula
open Finset

theorem valuation_zero_off_support (q : ℚ) (p : ℕ) (hp : p.Prime)
 (h : p∉primeSupport q) : padicValRat p q=0 := by
 have hn : q.num.natAbs.factorization p=0 := by
   apply Finsupp.notMem_support_iff.mp
   exact fun hh => h (mem_union_left _ hh)
 have hd : q.den.factorization p=0 := by
   apply Finsupp.notMem_support_iff.mp
   exact fun hh => h (mem_union_right _ hh)
 rw [Nat.factorization_def _ hp] at hn hd
 simp [padicValRat,padicValInt,hn,hd]

/-- Extend the product formula to a prescribed finite prime set; primes outside it
may be discarded only after their valuations are proved nonnegative. -/
theorem finite_prime_lower (q : ℚ) (hq : q≠0) (S : Finset ℕ) (w : ℕ → ℝ)
 (hS : ∀ p∈S,p.Prime)
 (hw : ∀ p∈S,w p≤(padicValRat p q:ℝ))
 (hout : ∀ p,p.Prime → p∉S → 0≤padicValRat p q) :
 ∑p∈S,w p*Real.log p ≤ Real.log |(q:ℝ)| := by
 rw [rational_log_product_formula q hq]
 have he : (∑p∈primeSupport q,(padicValRat p q:ℝ)*Real.log p)=
   ∑p∈S∪primeSupport q,(padicValRat p q:ℝ)*Real.log p := by
   apply sum_subset subset_union_right
   intro p hp hn
   have hps : p∈S := (mem_union.mp hp).resolve_right hn
   rw [valuation_zero_off_support q p (hS p hps) hn]
   simp
 rw [he]
 apply le_trans (sum_le_sum (fun p hp =>
   mul_le_mul_of_nonneg_right (hw p hp) (Real.log_nonneg (by exact_mod_cast (hS p hp).one_le))))
 apply sum_le_sum_of_subset_of_nonneg subset_union_left
 intro p hp hn
 have hpr := support_prime q p ((mem_union.mp hp).resolve_left hn)
 exact mul_nonneg (by exact_mod_cast hout p hpr hn)
   (Real.log_nonneg (by exact_mod_cast hpr.one_le))

#print axioms finite_prime_lower
end OddZeta.FourValue.ProductFormula

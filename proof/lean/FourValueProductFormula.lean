import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-! The rational product formula used by the determinant contradiction,
with Mathlib's actual rational numbers and `padicValRat`. -/
open scoped BigOperators
namespace OddZeta.FourValue.ProductFormula

def primeSupport (q : ℚ) : Finset ℕ :=
  q.num.natAbs.factorization.support ∪ q.den.factorization.support

theorem log_nat_on_superset (n : ℕ) (S : Finset ℕ)
    (hs : n.factorization.support ⊆ S) :
    Real.log (n : ℝ) = ∑ p ∈ S, (n.factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply Finset.sum_subset hs
  intro p _ hp
  have hz : n.factorization p = 0 := by
    by_contra hh
    exact hp (Finsupp.mem_support_iff.mpr hh)
  simp only [hz, Nat.cast_zero, zero_mul]

theorem support_prime (q : ℚ) (p : ℕ) (hp : p ∈ primeSupport q) : p.Prime := by
  simp only [primeSupport, Finset.mem_union, Nat.support_factorization] at hp
  rcases hp with hp | hp
  · exact Nat.prime_of_mem_primeFactors hp
  · exact Nat.prime_of_mem_primeFactors hp

theorem rational_log_product_formula (q : ℚ) (hq : q ≠ 0) :
    Real.log |(q : ℝ)| =
      ∑ p ∈ primeSupport q, (padicValRat p q : ℝ) * Real.log p := by
  have hn : q.num ≠ 0 := fun h => hq (Rat.zero_of_num_zero h)
  have hnR : (q.num : ℝ) ≠ 0 := by exact_mod_cast hn
  have hdR : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have habs : (q.num.natAbs : ℝ) = |(q.num : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs q.num)
  have hlog : Real.log |(q : ℝ)| =
      Real.log (q.num.natAbs : ℝ) - Real.log (q.den : ℝ) := by
    rw [Rat.cast_def, abs_div, abs_of_pos (by exact_mod_cast q.pos : (0:ℝ)<q.den),
      Real.log_div (abs_ne_zero.mpr hnR) hdR, ← habs]
  rw [hlog,
    log_nat_on_superset q.num.natAbs (primeSupport q) Finset.subset_union_left,
    log_nat_on_superset q.den (primeSupport q) Finset.subset_union_right,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := support_prime q p hp
  rw [Nat.factorization_def _ hprime, Nat.factorization_def _ hprime]
  simp only [padicValRat, padicValInt, Int.cast_sub, Int.cast_natCast, sub_mul]

#print axioms rational_log_product_formula
end OddZeta.FourValue.ProductFormula

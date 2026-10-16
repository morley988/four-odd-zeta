import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Initial formal components for the four-value determinant argument.
This file does NOT assert an unconditional zeta irrationality theorem.
The analytic, arithmetic and nonvanishing inputs remain separate obligations.
No `sorry`, new axiom, or `native_decide` is used.
-/

namespace OddZeta.FourValue

def endpoints : List ℕ :=
  [67,67,67,67,67,63,60,58,57,54,52,49,47,44,42]

def tailEndpoints : List ℕ := [63,60,58,57,54,52,49,47,44,42]

theorem endpoint_sum : endpoints.sum = 861 := by decide
theorem tail_sum : tailEndpoints.sum = 526 := by decide
theorem endpoint_count : endpoints.length = 15 := by decide
theorem beta_identity : endpoints.sum - 5 * 100 = 361 := by decide

def realUpper : ℚ := -577853339 / 50000000
def arithmeticLower : ℚ := -459446563841 / 40000000000
def certifiedGap : ℚ := 2836107359 / 40000000000

theorem gap_identity : arithmeticLower - realUpper = certifiedGap := by
  norm_num [arithmeticLower, realUpper, certifiedGap]

theorem gap_positive : 0 < certifiedGap := by norm_num [certifiedGap]

theorem strict_gap : realUpper < arithmeticLower := by
  norm_num [realUpper, arithmeticLower]

theorem normalized_arithmetic_certificate :
    ((-458183063841 / 4000000 : ℚ) - 2527 / 8) / 10000 = arithmeticLower := by
  norm_num [arithmeticLower]

theorem small_interval_certificate :
    -(35 : ℚ) * (361 / 2) * (1 / 20) = -2527 / 8 := by norm_num

theorem capacity_margin : (361 / 200 : ℚ) < 526 / 100 := by norm_num

/-- Degree budget in the truncated Hankel-to-Pearson implication. -/
theorem pearson_degree_budget (m r s : ℕ) (hs : s ≤ r) (hr : r + 4 ≤ m) :
    2 * s + 8 ≤ 2 * m - (r - s) := by omega

theorem initial_agreement_budget (m r s : ℕ)
    (hs : s ≤ r) (hr : r + 4 ≤ m) :
    8 ≤ 2 * m - (r - s) := by omega

theorem matrix_degree_budget (n : ℕ) :
    2 * ((361 * n) / 2) ≤ 361 * n := by omega

/-- A rank exclusion stated in the form used by the manuscript. -/
theorem rank_at_least (m r : ℕ) (hexclude : ¬ (r + 4 ≤ m)) :
    m + 1 - 4 ≤ r := by omega

/-- Elementary quadratic valuation cost obtained by summing row/column orders. -/
theorem bad_minor_cost (m lam : ℤ) :
    m * (lam - 4) + m * (m - 1) = m * m + (lam - 5) * m := by ring

theorem good_minor_cost (m lam : ℤ) :
    m * (lam + 1) + m * (m - 1) = m * m + lam * m := by ring

theorem bad_cost_lower (m lam : ℝ) (hm : 0 ≤ m) (hlam : -30 ≤ lam) :
    m ^ 2 - 35 * m ≤ m ^ 2 + (lam - 5) * m := by nlinarith

/-- Interpolating valid endpoint bounds is valid when the potential masses
are interpolated linearly.  This is pointwise in the contour parameter. -/
theorem interpolate_upper (t a b va vb : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : a ≤ va) (hb : b ≤ vb) :
    (1-t)*a + t*b ≤ (1-t)*va + t*vb := by
  exact add_le_add (mul_le_mul_of_nonneg_left ha (by linarith))
    (mul_le_mul_of_nonneg_left hb ht0)

/-- A precise conditional final comparison, without hiding the analytic inputs. -/
theorem no_eventual_two_sided_rates (x errLo errHi : ℕ → ℝ)
    (hlo : ∀ᶠ n in Filter.atTop, (arithmeticLower : ℝ) - errLo n ≤ x n)
    (hhi : ∀ᶠ n in Filter.atTop, x n ≤ (realUpper : ℝ) + errHi n)
    (helo : Filter.Tendsto errLo Filter.atTop (nhds 0))
    (hehi : Filter.Tendsto errHi Filter.atTop (nhds 0)) : False := by
  have hgap : (0 : ℝ) < (arithmeticLower : ℝ) - (realUpper : ℝ) := by
    norm_num [arithmeticLower, realUpper]
  have hsum : Filter.Tendsto (fun n => errLo n + errHi n)
      Filter.atTop (nhds 0) := by simpa using helo.add hehi
  have hevent := (tendsto_order.1 hsum).2
    ((arithmeticLower : ℝ) - (realUpper : ℝ)) hgap
  obtain ⟨n,hnlo,hnhi,hne⟩ := (hlo.and (hhi.and hevent)).exists
  linarith

#print axioms endpoint_sum
#print axioms strict_gap
#print axioms pearson_degree_budget
#print axioms interpolate_upper
#print axioms no_eventual_two_sided_rates

end OddZeta.FourValue

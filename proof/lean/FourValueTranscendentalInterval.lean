import FourValueTranscendental
import Mathlib.Data.Rat.Floor

namespace OddZeta.FourValue.Transcendental

/-- Rational interval arithmetic with explicit outward rounding. -/
structure QInterval where
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

namespace QInterval
noncomputable def Contains (a : QInterval) (x : ℝ) : Prop := (a.lo:ℝ) ≤ x ∧ x ≤ (a.hi:ℝ)

def point (q : ℚ) : QInterval := ⟨q,q⟩
def add (a b : QInterval) : QInterval := ⟨a.lo+b.lo,a.hi+b.hi⟩
def neg (a : QInterval) : QInterval := ⟨-a.hi,-a.lo⟩
def sub (a b : QInterval) : QInterval := a.add b.neg

def scale (q : ℚ) (a : QInterval) : QInterval :=
  if 0 ≤ q then ⟨q*a.lo,q*a.hi⟩ else ⟨q*a.hi,q*a.lo⟩

def mul (a b : QInterval) : QInterval :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩

def round (S : ℕ) (a : QInterval) : QInterval :=
  ⟨(⌊(S:ℚ)*a.lo⌋:ℚ)/S, (⌈(S:ℚ)*a.hi⌉:ℚ)/S⟩

theorem point_contains (q : ℚ) : (point q).Contains (q:ℝ) := ⟨le_rfl,le_rfl⟩

theorem add_contains {a b : QInterval} {x y : ℝ} (ha : a.Contains x) (hb : b.Contains y) :
    (a.add b).Contains (x+y) := by
  dsimp [Contains,add] at *
  push_cast
  exact ⟨add_le_add ha.1 hb.1, add_le_add ha.2 hb.2⟩

theorem neg_contains {a : QInterval} {x : ℝ} (ha : a.Contains x) :
    a.neg.Contains (-x) := by
  dsimp [Contains,neg] at *
  push_cast
  exact ⟨neg_le_neg ha.2,neg_le_neg ha.1⟩

theorem sub_contains {a b : QInterval} {x y : ℝ} (ha : a.Contains x) (hb : b.Contains y) :
    (a.sub b).Contains (x-y) := by simpa [sub,sub_eq_add_neg] using add_contains ha (neg_contains hb)

theorem scale_contains (q : ℚ) {a : QInterval} {x : ℝ} (ha : a.Contains x) :
    (a.scale q).Contains ((q:ℝ)*x) := by
  dsimp [scale, Contains] at *
  split_ifs with hq
  · have hq' : (0:ℝ) ≤ q := by exact_mod_cast hq
    push_cast
    exact ⟨mul_le_mul_of_nonneg_left ha.1 hq',mul_le_mul_of_nonneg_left ha.2 hq'⟩
  · have hq' : (q:ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hq)
    push_cast
    exact ⟨mul_le_mul_of_nonpos_left ha.2 hq',mul_le_mul_of_nonpos_left ha.1 hq'⟩

theorem round_contains (S : ℕ) (hS : 0 < S) {a : QInterval} {x : ℝ} (ha : a.Contains x) :
    (a.round S).Contains x := by
  have hS' : (0:ℚ) < S := by exact_mod_cast hS
  have hl : ((⌊(S:ℚ)*a.lo⌋:ℚ)/S) ≤ a.lo := by
    rw [div_le_iff₀ hS', mul_comm a.lo]
    exact Int.floor_le _
  have hh : a.hi ≤ ((⌈(S:ℚ)*a.hi⌉:ℚ)/S) := by
    rw [le_div_iff₀ hS', mul_comm a.hi]
    exact Int.le_ceil _
  change (((⌊(S:ℚ)*a.lo⌋:ℚ)/S:ℚ):ℝ) ≤ x ∧ x ≤ (((⌈(S:ℚ)*a.hi⌉:ℚ)/S:ℚ):ℝ)
  exact ⟨le_trans (by exact_mod_cast hl) ha.1,le_trans ha.2 (by exact_mod_cast hh)⟩

theorem scalar_bounds (a b c x : ℝ) (hx : b ≤ x ∧ x ≤ c) :
    min (a*b) (a*c) ≤ a*x ∧ a*x ≤ max (a*b) (a*c) := by
  by_cases ha : 0 ≤ a
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hx.1 ha),
      (mul_le_mul_of_nonneg_left hx.2 ha).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hx.2 (le_of_not_ge ha)),
      (mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge ha)).trans (le_max_left _ _)⟩

theorem mul_contains {a b : QInterval} {x y : ℝ} (ha : a.Contains x) (hb : b.Contains y) :
    (a.mul b).Contains (x*y) := by
  have h1 := scalar_bounds (a.lo:ℝ) b.lo b.hi y hb
  have h2 := scalar_bounds (a.hi:ℝ) b.lo b.hi y hb
  have h3 := scalar_bounds y a.lo a.hi x ha
  simp only [mul_comm y] at h3
  dsimp [Contains,mul]
  push_cast
  exact ⟨(min_le_min h1.1 h2.1).trans h3.1,h3.2.trans (max_le_max h1.2 h2.2)⟩

/-- State = current odd power and accumulated sum, rounded after every operation. -/
def seriesState (S : ℕ) (c : ℕ → ℚ) (X X2 : QInterval) : ℕ → QInterval × QInterval
  | 0 => (X, point 0)
  | n+1 =>
    let st := seriesState S c X X2 n
    ((st.1.mul X2).round S, (st.2.add ((st.1.scale (c n)).round S)).round S)

theorem seriesState_contains (S : ℕ) (hS : 0 < S) (c : ℕ → ℚ)
    (X X2 : QInterval) (x : ℝ) (hx : X.Contains x) (hx2 : X2.Contains (x^2)) (n : ℕ) :
    (seriesState S c X X2 n).1.Contains (x^(2*n+1)) ∧
    (seriesState S c X X2 n).2.Contains (∑ j ∈ Finset.range n, (c j:ℝ)*x^(2*j+1)) := by
  induction n with
  | zero => simpa [seriesState,point,Contains] using hx
  | succ n ih =>
    have hp := round_contains S hS (mul_contains ih.1 hx2)
    have hs := round_contains S hS (add_contains ih.2 (round_contains S hS (scale_contains (c n) ih.1)))
    constructor
    · convert hp using 1
      congr 1
      rw [← pow_add]
      congr 1
    · simpa only [seriesState,Finset.sum_range_succ] using hs

def series (S n : ℕ) (c : ℕ → ℚ) (q : ℚ) : QInterval :=
  (seriesState S c ((point q).round S) (((point q).round S).mul ((point q).round S) |>.round S) n).2

theorem series_contains (S n : ℕ) (hS : 0 < S) (c : ℕ → ℚ) (q : ℚ) :
    (series S n c q).Contains (∑ j ∈ Finset.range n, (c j:ℝ)*(q:ℝ)^(2*j+1)) := by
  have hq := round_contains S hS (point_contains q)
  exact (seriesState_contains S hS c _ _ _ hq
    (by simpa [pow_two] using round_contains S hS (mul_contains hq hq)) n).2

end QInterval
end OddZeta.FourValue.Transcendental

import FourValueFastInterval

namespace OddZeta.FourValue.Fast
open OddZeta.FourValue.Transcendental
open Finset QInterval

def logUnitInterval (S n : ℕ) (q : ℚ) : QInterval :=
  (((Interval.series S n false ((q-1)/(q+1))).toQ S).scale 2).add
    ⟨0,2*(1/3:ℚ)^(2*n+1)/(1-(1/3:ℚ)^2)⟩

theorem logUnitInterval_contains (S n : ℕ) (hS : 0 < S) (q : ℚ)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    (logUnitInterval S n q).Contains (Real.log (q:ℝ)) := by
  let t : ℚ := (q-1)/(q+1)
  have ht0 : (0:ℝ) ≤ (t:ℝ) := by
    have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hq1) (by linarith)
    exact_mod_cast ht
  have ht1 : (t:ℝ) ≤ 1/3 := by
    have ht : t ≤ 1/3 := by dsimp [t]; rw [div_le_iff₀ (by linarith : (0:ℚ) < q+1)]; linarith
    have hc : (t:ℝ) ≤ ((1/3:ℚ):ℝ) := Rat.cast_le.mpr ht
    norm_num at hc
    exact hc
  have hser := scale_contains 2 (Interval.toQ_contains S hS (Interval.log_series_contains S n hS t))
  have hlog := logRat_enclosure n q hq1
  have hrem : 2*(t:ℝ)^(2*n+1)/(1-(t:ℝ)^2) ≤
      2*(1/3:ℝ)^(2*n+1)/(1-(1/3:ℝ)^2) := by
    gcongr
  dsimp [Contains,logUnitInterval,add,scale] at hser ⊢
  norm_num only [show (0:ℚ) ≤ 2 by norm_num, ↓reduceIte, Rat.cast_zero, Rat.cast_add, add_zero] at hser ⊢
  have heq : (logRat n t : ℝ) = 2*∑ j ∈ range n, (t:ℝ)^(2*j+1)/(2*j+1) := by simp [logRat]
  change (logRat n t : ℝ) ≤ Real.log (q:ℝ) ∧
    Real.log (q:ℝ) ≤ ((logRat n t+2*t^(2*n+1)/(1-t^2):ℚ):ℝ) at hlog
  rw [heq] at hlog
  push_cast at hlog hser ⊢
  rw [heq] at hlog
  change _ ≤ Real.log (q:ℝ) ∧ Real.log (q:ℝ) ≤ 2*((Interval.series S n false t).toQ S).hi + 2*(1/3:ℝ)^(2*n+1)/(8/9)
  norm_num only [show (1-(1/3:ℝ)^2) = 8/9 by norm_num] at hrem
  constructor
  · exact hser.1.trans hlog.1
  · linarith [hser.2, hlog.2]

def atanSmallInterval (S n : ℕ) (q : ℚ) : QInterval :=
  ((Interval.series S n true q).toQ S).add
    ⟨-(1/2:ℚ)^(2*n+1),(1/2:ℚ)^(2*n+1)⟩

theorem atanSmallInterval_contains (S n : ℕ) (hS : 0 < S) (q : ℚ) (hq : |q| ≤ 1/2) :
    (atanSmallInterval S n q).Contains (Real.arctan (q:ℝ)) := by
  have hs := Interval.toQ_contains S hS (Interval.atan_series_contains S n hS q)
  have hr := atan_remainder_bound n (q:ℝ)
  have hp : |(q:ℝ)|^(2*n+1) ≤ (1/2:ℝ)^(2*n+1) := by
    gcongr
    have hc : ((|q|:ℚ):ℝ) ≤ ((1/2:ℚ):ℝ) := Rat.cast_le.mpr hq
    norm_num at hc
    exact hc
  have hab := abs_le.mp (hr.trans hp)
  dsimp [Contains,atanSmallInterval,add] at hs ⊢
  push_cast
  constructor <;> linarith

/-- Fuel only limits computation: failure returns none and never supplies an enclosure. -/
def logInterval (S n : ℕ) : ℕ → ℚ → Option QInterval
  | 0, q => if 1 ≤ q ∧ q ≤ 2 then some (logUnitInterval S n q) else none
  | fuel+1, q =>
    if q ≤ 0 then none else if q < 1 then
      (logInterval S n fuel q⁻¹).map QInterval.neg
    else if 2 < q then
      (logInterval S n fuel (q/2)).map (fun a => a.add (logUnitInterval S n 2))
    else some (logUnitInterval S n q)

theorem logInterval_contains (S n : ℕ) (hS : 0 < S) (fuel : ℕ) (q : ℚ) (a : QInterval)
    (h : logInterval S n fuel q = some a) : a.Contains (Real.log (q:ℝ)) := by
  induction fuel generalizing q a with
  | zero =>
    dsimp [logInterval] at h
    split_ifs at h with hq
    · cases h
      exact logUnitInterval_contains S n hS q hq.1 hq.2
  | succ fuel ih =>
    dsimp [logInterval] at h
    split_ifs at h with hq0 hq1 hq2
    · cases he : logInterval S n fuel q⁻¹ with
      | none => simp [he] at h
      | some b =>
        simp only [he, Option.map_some, Option.some.injEq] at h
        subst a
        have hb := neg_contains (ih _ _ he)
        simpa using hb
    · cases he : logInterval S n fuel (q/2) with
      | none => simp [he] at h
      | some b =>
        simp only [he, Option.map_some, Option.some.injEq] at h
        subst a
        have hb := add_contains (ih _ _ he) (logUnitInterval_contains S n hS 2 (by norm_num) (by norm_num))
        have hq : (q:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_not_ge hq0))
        have hlog : Real.log ((q/2:ℚ):ℝ)+Real.log 2=Real.log (q:ℝ) := by
          push_cast
          rw [Real.log_div hq (by norm_num)]
          ring
        norm_num only [Rat.cast_ofNat] at hb
        simpa only [hlog] using hb
    · cases h
      exact logUnitInterval_contains S n hS q (le_of_not_gt hq1) (le_of_not_gt hq2)

def atanUnitInterval (S n : ℕ) (P : QInterval) (q : ℚ) : QInterval :=
  if q ≤ 1/2 then atanSmallInterval S n q
  else (P.scale (1/4)).add (atanSmallInterval S n ((q-1)/(q+1)))

theorem atanUnitInterval_contains (S n : ℕ) (hS : 0 < S) (P : QInterval)
    (hP : P.Contains Real.pi) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (atanUnitInterval S n P q).Contains (Real.arctan (q:ℝ)) := by
  dsimp [atanUnitInterval]
  split_ifs with hq
  · apply atanSmallInterval_contains S n hS q
    rwa [abs_of_nonneg hq0]
  · have ht : |(q-1)/(q+1)| ≤ (1/2:ℚ) := by
      rw [abs_le]
      have hd : (0:ℚ) < q+1 := by linarith
      constructor
      · rw [le_div_iff₀ hd]; linarith
      · rw [div_le_iff₀ hd]; linarith
    have h := add_contains (scale_contains (1/4) hP) (atanSmallInterval_contains S n hS _ ht)
    have he := atan_reduce_quarter (q:ℝ) (by exact_mod_cast hq0)
    convert h using 1
    push_cast
    rw [he]
    ring

def atanPositiveInterval (S n : ℕ) (P : QInterval) (q : ℚ) : QInterval :=
  if q ≤ 1 then atanUnitInterval S n P q
  else (P.scale (1/2)).sub (atanUnitInterval S n P q⁻¹)

theorem atanPositiveInterval_contains (S n : ℕ) (hS : 0 < S) (P : QInterval)
    (hP : P.Contains Real.pi) (q : ℚ) (hq0 : 0 ≤ q) :
    (atanPositiveInterval S n P q).Contains (Real.arctan (q:ℝ)) := by
  dsimp [atanPositiveInterval]
  split_ifs with hq
  · exact atanUnitInterval_contains S n hS P hP q hq0 hq
  · have hqpos : (0:ℚ) < q := by linarith
    have hi0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0
    have hi1 : q⁻¹ ≤ 1 := (inv_le_one₀ hqpos).mpr (by linarith)
    have h := sub_contains (scale_contains (1/2) hP) (atanUnitInterval_contains S n hS P hP _ hi0 hi1)
    have he := atan_reduce_inverse (q:ℝ) (by exact_mod_cast hqpos)
    convert h using 1
    push_cast
    rw [he]
    ring

def atanInterval (S n : ℕ) (P : QInterval) (q : ℚ) : QInterval :=
  if 0 ≤ q then atanPositiveInterval S n P q else (atanPositiveInterval S n P (-q)).neg

theorem atanInterval_contains (S n : ℕ) (hS : 0 < S) (P : QInterval)
    (hP : P.Contains Real.pi) (q : ℚ) :
    (atanInterval S n P q).Contains (Real.arctan (q:ℝ)) := by
  dsimp [atanInterval]
  split_ifs with hq
  · exact atanPositiveInterval_contains S n hS P hP q hq
  · have h := neg_contains (atanPositiveInterval_contains S n hS P hP (-q) (by linarith))
    simpa using h

end OddZeta.FourValue.Fast

import FourValueFastEvaluator

namespace OddZeta.FourValue.Fast
open OddZeta.FourValue.Transcendental QInterval

/-- Accumulate the binary exponent, so log(2) is enclosed only once per input. -/
def reduceLog : ℕ → ℚ → Option (ℤ × ℚ)
  | 0, q => if 1 ≤ q ∧ q ≤ 2 then some (0,q) else none
  | fuel+1, q =>
    if q ≤ 0 then none else if q < 1 then
      (reduceLog fuel (q*2)).map (fun p => (p.1-1,p.2))
    else if 2 < q then
      (reduceLog fuel (q/2)).map (fun p => (p.1+1,p.2))
    else some (0,q)

theorem reduceLog_sound (fuel : ℕ) (q : ℚ) (p : ℤ × ℚ)
    (h : reduceLog fuel q = some p) :
    1 ≤ p.2 ∧ p.2 ≤ 2 ∧ Real.log (q:ℝ) = (p.1:ℝ)*Real.log 2 + Real.log (p.2:ℝ) := by
  induction fuel generalizing q p with
  | zero =>
    dsimp [reduceLog] at h
    split_ifs at h with hq
    cases h
    exact ⟨hq.1,hq.2,by simp⟩
  | succ fuel ih =>
    dsimp [reduceLog] at h
    split_ifs at h with hq0 hq1 hq2
    · cases he : reduceLog fuel (q*2) with
      | none => simp [he] at h
      | some b =>
        simp only [he,Option.map_some,Option.some.injEq] at h
        subst p
        obtain ⟨hb1,hb2,hb3⟩ := ih _ _ he
        refine ⟨hb1,hb2,?_⟩
        have hq : (q:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_not_ge hq0))
        push_cast at hb3 ⊢
        rw [Real.log_mul hq (by norm_num)] at hb3
        linarith
    · cases he : reduceLog fuel (q/2) with
      | none => simp [he] at h
      | some b =>
        simp only [he,Option.map_some,Option.some.injEq] at h
        subst p
        obtain ⟨hb1,hb2,hb3⟩ := ih _ _ he
        refine ⟨hb1,hb2,?_⟩
        have hq : (q:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_not_ge hq0))
        push_cast at hb3 ⊢
        rw [Real.log_div hq (by norm_num)] at hb3
        linarith
    · cases h
      exact ⟨le_of_not_gt hq1,le_of_not_gt hq2,by simp⟩

def reducedLogInterval (S n fuel : ℕ) (q : ℚ) : Option QInterval :=
  (reduceLog fuel q).map (fun p =>
    ((logUnitInterval S n 2).scale (p.1:ℚ)).add (logUnitInterval S n p.2))

theorem reducedLogInterval_contains (S n : ℕ) (hS : 0 < S) (fuel : ℕ)
    (q : ℚ) (a : QInterval) (h : reducedLogInterval S n fuel q = some a) :
    a.Contains (Real.log (q:ℝ)) := by
  dsimp [reducedLogInterval] at h
  cases he : reduceLog fuel q with
  | none => simp [he] at h
  | some p =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst a
    obtain ⟨h1,h2,h3⟩ := reduceLog_sound fuel q p he
    have hp := add_contains (scale_contains (p.1:ℚ)
      (logUnitInterval_contains S n hS 2 (by norm_num) (by norm_num)))
      (logUnitInterval_contains S n hS p.2 h1 h2)
    rw [h3]
    simpa using hp

end OddZeta.FourValue.Fast

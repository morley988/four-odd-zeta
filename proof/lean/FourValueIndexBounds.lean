import FourValuePadicMinors
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! Distinct row and column indices force the quadratic local minor cost. -/
namespace OddZeta.FourValue
open scoped BigOperators

 theorem strictMono_fin_nat_lower {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f)
    (i : Fin n) : i.val ≤ f i := by
  rcases i with ⟨i, hi⟩
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
      have hi' : i < n := by omega
      have hprev := ih hi'
      have hstep := hf (show (⟨i, hi'⟩ : Fin n) < ⟨i+1, hi⟩ by simp)
      simpa using (Nat.succ_le_of_lt (lt_of_le_of_lt hprev hstep))

/-- Any injection of `k` indices into the naturals has total at least the
sum of `0,...,k-1`, even if the selected indices are not listed in order. -/
theorem sum_injective_nat_lower {k : ℕ} (f : Fin k → ℕ) (hf : Function.Injective f) :
    (∑ i : Fin k, i.val) ≤ ∑ i : Fin k, f i := by
  classical
  let s := Finset.univ.image f
  have hs : s.card = k := by simp [s, Finset.card_image_of_injective _ hf]
  let e := s.orderEmbOfFin hs
  have hsum : (∑ i : Fin k, e i) = ∑ i : Fin k, f i := by
    calc
      _ = ∑ a ∈ s, a := by
        rw [← Finset.image_orderEmbOfFin_univ s hs, Finset.sum_image]
        exact fun a _ b _ h => e.injective h
      _ = _ := by
        dsimp [s]
        rw [Finset.sum_image]
        exact fun a _ b _ h => hf h
  rw [← hsum]
  exact Finset.sum_le_sum (fun i _ => strictMono_fin_nat_lower e e.strictMono i)

/-- Twice the index sum avoids division and coercion issues. -/
theorem twice_sum_injective_nat_lower {k : ℕ} (f : Fin k → ℕ)
    (hf : Function.Injective f) :
    (k : ℤ) * ((k : ℤ)-1) ≤ 2 * ∑ i : Fin k, (f i : ℤ) := by
  have h := sum_injective_nat_lower f hf
  have hcast : (∑ i : Fin k, (i.val : ℤ)) ≤ ∑ i : Fin k, (f i : ℤ) := by
    exact_mod_cast h
  have hform : 2 * ∑ i : Fin k, (i.val : ℤ) = (k : ℤ) * ((k : ℤ)-1) := by
    clear f hf h hcast
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        push_cast
        nlinarith
  linarith

/-- The local quadratic valuation bound follows for every selected minor,
with no restriction to consecutive or principal rows and columns. -/
theorem padicLower_det_distinct_indices {p k : ℕ} [Fact p.Prime]
    (A : Matrix (Fin k) (Fin k) ℚ) (row col : Fin k → ℕ)
    (hr : Function.Injective row) (hc : Function.Injective col) (c : ℤ)
    (hA : ∀ i j, PadicLower p ((row i : ℤ) + col j + c) (A i j)) :
    PadicLower p ((k : ℤ)^2 + (c-1)*k) A.det := by
  have h := padicLower_det_weighted A (fun i => (row i : ℤ))
    (fun j => (col j : ℤ)) c hA
  apply h.mono
  simp only [Fintype.card_fin]
  have hr' := twice_sum_injective_nat_lower row hr
  have hc' := twice_sum_injective_nat_lower col hc
  nlinarith

/-- In the bad-prime cell, entry weight `lambda+i+j-4` gives exactly
`k^2+(lambda-5)k` for the determinant. -/
theorem padicLower_det_bad_cell {p k : ℕ} [Fact p.Prime]
    (A : Matrix (Fin k) (Fin k) ℚ) (row col : Fin k → ℕ)
    (hr : Function.Injective row) (hc : Function.Injective col) (lambda : ℤ)
    (hA : ∀ i j, PadicLower p ((row i : ℤ) + col j + lambda - 4) (A i j)) :
    PadicLower p ((k : ℤ)^2 + (lambda-5)*k) A.det := by
  have h := padicLower_det_distinct_indices A row col hr hc (lambda-4)
    (fun i j => by convert hA i j using 1 <;> ring)
  convert h using 1 <;> ring

end OddZeta.FourValue

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! Valuation bounds for actual rational determinants. Zero entries are
handled explicitly, since Mathlib's `padicValRat p 0` is defined to be zero. -/

namespace OddZeta.FourValue
open scoped BigOperators

def PadicLower (p : ℕ) (b : ℤ) (q : ℚ) : Prop := q = 0 ∨ b ≤ padicValRat p q

variable {p : ℕ} [Fact p.Prime]

theorem PadicLower.zero (b : ℤ) : PadicLower p b 0 := Or.inl rfl

theorem PadicLower.mono {a b : ℤ} {q : ℚ}
    (h : PadicLower p b q) (hab : a ≤ b) : PadicLower p a q :=
  h.elim Or.inl (fun hq => Or.inr (hab.trans hq))

theorem PadicLower.of_ne_zero {b : ℤ} {q : ℚ}
    (h : PadicLower p b q) (hq : q ≠ 0) : b ≤ padicValRat p q :=
  h.resolve_left hq

theorem PadicLower.neg {b : ℤ} {q : ℚ} (h : PadicLower p b q) :
    PadicLower p b (-q) := by
  simpa [PadicLower] using h

theorem PadicLower.add {b : ℤ} {q r : ℚ}
    (hq : PadicLower p b q) (hr : PadicLower p b r) :
    PadicLower p b (q+r) := by
  rcases hq with rfl | hq
  · simpa using hr
  rcases hr with rfl | hr
  · exact Or.inr (by simpa using hq)
  by_cases hz : q+r = 0
  · exact Or.inl hz
  · exact Or.inr ((le_min hq hr).trans (padicValRat.min_le_padicValRat_add hz))

theorem PadicLower.mul {a b : ℤ} {q r : ℚ}
    (hq : PadicLower p a q) (hr : PadicLower p b r) :
    PadicLower p (a+b) (q*r) := by
  by_cases hq0 : q=0
  · simp [hq0, PadicLower]
  by_cases hr0 : r=0
  · simp [hr0, PadicLower]
  right
  rw [padicValRat.mul hq0 hr0]
  exact add_le_add (hq.of_ne_zero hq0) (hr.of_ne_zero hr0)

theorem padicLower_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (b : ℤ)
    (h : ∀ i ∈ s, PadicLower p b (f i)) : PadicLower p b (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (PadicLower.zero (p := p) b)
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

theorem padicLower_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (b : ι → ℤ)
    (h : ∀ i ∈ s, PadicLower p (b i) (f i)) :
    PadicLower p (∑ i ∈ s, b i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PadicLower]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      exact (h i (by simp)).mul (ih (fun j hj => h j (by simp [hj])))

theorem PadicLower.sign_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℚ} {b : ℤ} (h : PadicLower p b q) (σ : Equiv.Perm ι) :
    PadicLower p b (Equiv.Perm.sign σ • q) := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using h
  · simpa [hs] using h.neg

/-- Row and column valuation weights add in every determinant term. -/
theorem padicLower_det_weighted {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (row col : ι → ℤ) (c : ℤ)
    (hA : ∀ i j, PadicLower p (row i + col j + c) (A i j)) :
    PadicLower p ((∑ i, row i) + (∑ j, col j) + Fintype.card ι * c) A.det := by
  rw [Matrix.det_apply]
  apply padicLower_sum
  intro σ _
  apply PadicLower.sign_smul
  have h := padicLower_prod (p := p) Finset.univ
    (fun i => A (σ i) i) (fun i => row (σ i) + col i + c)
    (fun i _ => hA (σ i) i)
  simpa only [Finset.sum_add_distrib, Equiv.sum_comp, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] using h

/-- The bound is a statement about Mathlib's actual rational valuation once
the selected determinant is known to be nonzero. -/
theorem padicVal_det_weighted {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (row col : ι → ℤ) (c : ℤ)
    (hA : ∀ i j, PadicLower p (row i + col j + c) (A i j))
    (hdet : A.det ≠ 0) :
    (∑ i, row i) + (∑ j, col j) + Fintype.card ι * c ≤ padicValRat p A.det :=
  (padicLower_det_weighted A row col c hA).of_ne_zero hdet

end OddZeta.FourValue

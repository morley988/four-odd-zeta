import FourValueSeedSystem
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic

/-! Exact centered products, their shift identities, and the denominator
of the seed antidifference. These are identities of actual polynomials. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def centeredDenominator : ℕ → K[X]
  | 0 => X
  | a+1 => centeredDenominator a * (X-C ((a+1:ℕ):K)) * (X+C ((a+1:ℕ):K))

@[simp] theorem centeredDenominator_zero : centeredDenominator (K:=K) 0=X := rfl

theorem centeredDenominator_succ (a : ℕ) :
    centeredDenominator (K:=K) (a+1)=centeredDenominator a *
      (X^2-C (((a+1:ℕ):K)^2)) := by
  rw [centeredDenominator]
  simp only [map_pow]
  ring

theorem centeredDenominator_product (a : ℕ) :
    centeredDenominator (K:=K) a = X*∏ j ∈ Finset.range a,
      (X^2-C (((j+1:ℕ):K)^2)) := by
  induction a with
  | zero => simp
  | succ a ih => rw [centeredDenominator_succ,ih,Finset.prod_range_succ,mul_assoc]

theorem centeredDenominator_monic (a : ℕ) : (centeredDenominator (K:=K) a).Monic := by
  induction a with
  | zero => exact Polynomial.monic_X
  | succ a ih =>
      exact (ih.mul (Polynomial.monic_X_sub_C _)).mul (Polynomial.monic_X_add_C _)

theorem centeredDenominator_degree (a : ℕ) :
    (centeredDenominator (K:=K) a).natDegree=2*a+1 := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [centeredDenominator,
        ((centeredDenominator_monic a).mul (Polynomial.monic_X_sub_C _)).natDegree_mul
          (Polynomial.monic_X_add_C _),
        (centeredDenominator_monic a).natDegree_mul (Polynomial.monic_X_sub_C _),
        Polynomial.natDegree_X_sub_C,Polynomial.natDegree_X_add_C,ih]
      omega

/-- The centered product contains each integer root from -a to a once. -/
theorem centeredDenominator_eval_zero_iff (a : ℕ) (x : K) :
    (centeredDenominator a).eval x=0 ↔
      ∃ j : ℤ, -(a:ℤ)≤j ∧ j≤a ∧ x=(j:K) := by
  induction a with
  | zero =>
      simp only [centeredDenominator_zero,Polynomial.eval_X,Nat.cast_zero,Int.cast_zero,neg_zero]
      constructor
      · intro h
        exact ⟨0,le_refl _,le_refl _,by simpa using h⟩
      · rintro ⟨j,hj,hj',rfl⟩
        have : j=0 := le_antisymm hj' hj
        simp [this]
  | succ a ih =>
      rw [centeredDenominator,Polynomial.eval_mul,Polynomial.eval_mul,
        Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,
        mul_eq_zero,mul_eq_zero,ih]
      constructor
      · rintro ((⟨j,hj,hj',hx⟩ | hp) | hn)
        · exact ⟨j,by omega,by omega,hx⟩
        · refine ⟨a+1,by omega,by omega,?_⟩
          simpa using sub_eq_zero.mp hp
        · refine ⟨-(a+1),by omega,by omega,?_⟩
          simpa using eq_neg_of_add_eq_zero_left hn
      · rintro ⟨j,hj,hj',hx⟩
        by_cases hlow : -(a:ℤ)≤j
        · by_cases hhigh : j≤a
          · exact Or.inl (Or.inl ⟨j,hlow,hhigh,hx⟩)
          · have hjtop : j=(a:ℤ)+1 := by omega
            left; right
            rw [hx,hjtop]
            simp
        · have hjbottom : j=-((a:ℤ)+1) := by omega
          right
          rw [hx,hjbottom]
          simp

theorem centeredDenominator_eval_ne_zero_above (a : ℕ) (x : ℝ) (hx : (a:ℝ)<x) :
    (centeredDenominator (K:=ℝ) a).eval x≠0 := by
  intro hz
  obtain ⟨j,_,hj,hxj⟩ := (centeredDenominator_eval_zero_iff a x).mp hz
  have hjR : (j:ℝ)≤(a:ℝ) := by exact_mod_cast hj
  linarith

theorem centeredDenominator_eval_pos_above (a : ℕ) (x : ℝ) (hx : (a:ℝ)<x) :
    0<(centeredDenominator (K:=ℝ) a).eval x := by
  induction a with
  | zero => simpa using hx
  | succ a ih =>
      simp only [centeredDenominator,Polynomial.eval_mul,Polynomial.eval_sub,
        Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
      apply mul_pos
      · exact mul_pos (ih (by exact lt_trans (by exact_mod_cast Nat.lt_succ_self a) hx))
          (sub_pos.mpr hx)
      · have ha : (0:ℝ)≤((a+1:ℕ):ℝ) := Nat.cast_nonneg _
        linarith

/-- Exact cancellation of consecutive centered products. -/
theorem centeredDenominator_shift (a : ℕ) :
    (centeredDenominator (K:=K) a).comp (X+1)*(X-C (a:K)) =
      centeredDenominator a*(X+C ((a+1:ℕ):K)) := by
  induction a with
  | zero => simp [mul_comm]
  | succ a ih =>
      simp only [centeredDenominator,Polynomial.mul_comp,Polynomial.sub_comp,
        Polynomial.add_comp,Polynomial.X_comp,Polynomial.C_comp]
      have h₁ : (X+1-C ((a+1:ℕ):K):K[X])=X-C (a:K) := by
        simp [Nat.cast_add,map_add] <;> ring
      have h₂ : (X+1+C ((a+1:ℕ):K):K[X])=X+C ((a+1+1:ℕ):K) := by
        simp [Nat.cast_add,map_add] <;> ring
      rw [h₁,h₂]
      calc
        _ = ((centeredDenominator a).comp (X+1)*(X-C (a:K))) *
            (X-C ((a+1:ℕ):K))*(X+C ((a+1+1:ℕ):K)) := by ring
        _ = _ := by rw [ih]; ring

def seedTailDenominator : ℕ → K[X]
  | 0 => 1
  | b+1 => centeredDenominator b*(X-C ((b+1:ℕ):K))

theorem seedTailDenominator_monic (b : ℕ) : (seedTailDenominator (K:=K) b).Monic := by
  cases b with
  | zero => exact Polynomial.monic_one
  | succ b => exact (centeredDenominator_monic b).mul (Polynomial.monic_X_sub_C _)

theorem seedTailDenominator_degree (b : ℕ) :
    (seedTailDenominator (K:=K) b).natDegree=2*b := by
  cases b with
  | zero => simp [seedTailDenominator]
  | succ b =>
      rw [seedTailDenominator,
        (centeredDenominator_monic b).natDegree_mul (Polynomial.monic_X_sub_C _),
        centeredDenominator_degree,Polynomial.natDegree_X_sub_C]
      omega

theorem seedTailDenominator_factor (b : ℕ) :
    centeredDenominator (K:=K) b=(X+C (b:K))*seedTailDenominator b := by
  cases b with
  | zero => simp [seedTailDenominator]
  | succ b => simp only [centeredDenominator,seedTailDenominator]; ring

theorem seedTailDenominator_shift_factor (b : ℕ) :
    centeredDenominator (K:=K) b=(X-C (b:K))*(seedTailDenominator b).comp (X+1) := by
  cases b with
  | zero => simp [seedTailDenominator]
  | succ b =>
      simp only [seedTailDenominator,Polynomial.mul_comp,Polynomial.sub_comp,
        Polynomial.X_comp,Polynomial.C_comp]
      have h : (X+1-C ((b+1:ℕ):K):K[X])=X-C (b:K) := by
        simp [Nat.cast_add,map_add] <;> ring
      rw [h,centeredDenominator_shift,centeredDenominator]
      ring

theorem seedTailDenominator_eval_ne_zero (b : ℕ) (x : ℝ) (hx : (b:ℝ)<x) :
    (seedTailDenominator (K:=ℝ) b).eval x≠0 := by
  have h := centeredDenominator_eval_ne_zero_above b x hx
  rw [seedTailDenominator_factor,Polynomial.eval_mul] at h
  exact (mul_ne_zero_iff.mp h).2

end OddZeta.FourValue

import Mathlib.Tactic
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.NumberTheory.Padics.PadicVal.Basic

open scoped BigOperators
namespace OddZeta.Coefficients

/-- D^j clears the j-th normalized Taylor coefficient. -/
def Cleared (D : ℤ) (f : ℕ → ℚ) : Prop :=
  ∀ j, ∃ z : ℤ, (D:ℚ)^j * f j = z

def conv (f g : ℕ → ℚ) (j : ℕ) : ℚ :=
  ∑ ij ∈ Finset.antidiagonal j, f ij.1 * g ij.2

theorem cleared_geometric (D z : ℤ) (a : ℚ) (ha : (D:ℚ)*a=z) :
    Cleared D (fun j => a^j) := by
  intro j
  refine ⟨z^j, ?_⟩
  rw [← mul_pow, ha, Int.cast_pow]

theorem cleared_conv (D : ℤ) (f g : ℕ → ℚ) (hf : Cleared D f) (hg : Cleared D g) :
    Cleared D (conv f g) := by
  classical
  choose u hu using hf
  choose v hv using hg
  intro j
  refine ⟨∑ ij ∈ Finset.antidiagonal j, u ij.1 * v ij.2, ?_⟩
  simp only [conv, Finset.mul_sum, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hs := Finset.mem_antidiagonal.mp hij
  rw [← hu ij.1, ← hv ij.2, ← hs, pow_add]
  ring

theorem cleared_scalar (D z : ℤ) (f : ℕ → ℚ) (hf : Cleared D f) :
    Cleared D (fun j => (z:ℚ)*f j) := by
  intro j
  obtain ⟨m, hm⟩ := hf j
  refine ⟨z*m, ?_⟩
  push_cast
  calc
    _ = (z:ℚ)*((D:ℚ)^j*f j) := by ring
    _ = _ := by rw [hm]

def unitSeq (j : ℕ) : ℚ := if j=0 then 1 else 0

theorem cleared_unit (D : ℤ) : Cleared D unitSeq := by
  intro j
  by_cases hj : j=0
  · subst j; exact ⟨1, by simp [unitSeq]⟩
  · exact ⟨0, by simp [unitSeq, hj]⟩

def productSeq : List (ℕ → ℚ) → ℕ → ℚ
  | [] => unitSeq
  | f :: fs => conv f (productSeq fs)

theorem cleared_product (D : ℤ) (fs : List (ℕ → ℚ))
    (hfs : ∀ f ∈ fs, Cleared D f) : Cleared D (productSeq fs) := by
  induction fs with
  | nil => exact cleared_unit D
  | cons f fs ih =>
    exact cleared_conv D f _ (hfs f (by simp)) (ih (by intro g hg; exact hfs g (by simp [hg])))

/-- Coefficients of (1 + t/a)^(-1). -/
def reciprocalFactor (a : ℤ) (j : ℕ) : ℚ := (-((a:ℚ)⁻¹))^j

theorem cleared_reciprocalFactor (D a : ℤ) (ha : a ≠ 0) (hdiv : a ∣ D) :
    Cleared D (reciprocalFactor a) := by
  obtain ⟨z, hz⟩ := hdiv
  apply cleared_geometric D (-z)
  have haq : (a:ℚ) ≠ 0 := by exact_mod_cast ha
  rw [hz]
  push_cast
  field_simp

/-- A product of reciprocal factors with an integer residue has cleared coefficients. -/
theorem reciprocal_product_coefficients (D residue : ℤ) (offsets : List ℤ)
    (hnz : ∀ a ∈ offsets, a ≠ 0) (hdvd : ∀ a ∈ offsets, a ∣ D) :
    Cleared D (fun j => (residue:ℚ)*productSeq (offsets.map reciprocalFactor) j) := by
  apply cleared_scalar D residue
  apply cleared_product
  intro f hf
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hf
  exact cleared_reciprocalFactor D a (hnz a ha) (hdvd a ha)

/-- Legendre's factorial valuation simplifies to one quotient below p^2. -/
theorem factorial_valuation_below_square (p m : ℕ) [Fact p.Prime] (hm : m < p^2) :
    padicValNat p m.factorial = m/p := by
  by_cases hm0 : m = 0
  · simp [hm0]
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hlog : Nat.log p m < 2 := (Nat.log_lt_iff_lt_pow hp hm0).mpr hm
  rw [padicValNat_factorial hlog]
  norm_num [Finset.sum_Ico_succ_top]

/-- The binomial residue's valuation is a floor carry when its size is below p^2. -/
theorem binomial_valuation_below_square (p n k : ℕ) [Fact p.Prime]
    (hk : k ≤ n) (hn : n < p^2) :
    padicValNat p (n.choose k) = n/p-k/p-(n-k)/p := by
  rw [Nat.choose_eq_factorial_div_factorial hk,
    padicValNat.div_of_dvd (Nat.factorial_mul_factorial_dvd_factorial hk),
    padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
    factorial_valuation_below_square p n hn,
    factorial_valuation_below_square p k (by omega),
    factorial_valuation_below_square p (n-k) (by omega)]
  omega

#print axioms binomial_valuation_below_square
#print axioms cleared_conv
#print axioms reciprocal_product_coefficients
#print axioms factorial_valuation_below_square
end OddZeta.Coefficients

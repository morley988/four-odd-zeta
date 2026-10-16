import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Finset Set
namespace OddZeta.FourValue.Transcendental

/-- Rational polynomial used for the arctangent enclosure. -/
def atanPoly (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range n, (-1 : ℝ)^j * x^(2*j+1)/(2*j+1)

theorem atan_remainder_deriv (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t => Real.arctan t - atanPoly n t)
      ((-1 : ℝ)^n * x^(2*n)/(1+x^2)) x := by
  induction n with
  | zero => simpa [atanPoly] using Real.hasDerivAt_arctan x
  | succ n ih =>
    have hn : (2*(n:ℝ)+1) ≠ 0 := by positivity
    have hq : (1+x^2) ≠ 0 := by positivity
    have ht := (((hasDerivAt_id x).pow (2*n+1)).const_mul ((-1:ℝ)^n)).div_const
      (2*(n:ℝ)+1)
    have h := ih.sub ht
    convert! h using 1
    · ext t
      simp [atanPoly, sum_range_succ, Nat.cast_add, Nat.cast_mul]
      ring
    · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        Nat.add_sub_cancel, mul_one, id_eq, Pi.pow_apply]
      rw [show 2*(n+1)=2*n+2 by omega, pow_add, pow_succ]
      field_simp
      <;> ring

/-- A uniform remainder bound requiring only a power and rational arithmetic. -/
theorem atan_remainder_bound (n : ℕ) (x : ℝ) :
    |Real.arctan x - atanPoly n x| ≤ |x|^(2*n+1) := by
  have hb : ∀ t ∈ Icc (-|x|) |x|,
      ‖(-1:ℝ)^n * t^(2*n)/(1+t^2)‖ ≤ |x|^(2*n) := by
    intro t ht
    have ht' : |t| ≤ |x| := abs_le.mpr ht
    calc
      ‖(-1:ℝ)^n * t^(2*n)/(1+t^2)‖ = |t|^(2*n)/(1+t^2) := by
        simp [norm_div, norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1+t^2)]
      _ ≤ |t|^(2*n) := div_le_self (by positivity) (by nlinarith [sq_nonneg t])
      _ ≤ |x|^(2*n) := pow_le_pow_left₀ (abs_nonneg _) ht' _
  have h := (convex_Icc (-|x|) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (atan_remainder_deriv n t).hasDerivWithinAt) hb
    (by simp : (0:ℝ) ∈ Icc (-|x|) |x|)
    (by simp [le_abs_self, neg_le, neg_le_abs] : x ∈ Icc (-|x|) |x|)
  simpa [atanPoly, pow_succ] using h

/-- Rational series enclosure for a positive logarithm after reduction. -/
theorem log_enclosure (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) :
    2*(∑ j ∈ range n, t^(2*j+1)/(2*j+1)) ≤ Real.log ((1+t)/(1-t)) ∧
    Real.log ((1+t)/(1-t)) ≤
      2*(∑ j ∈ range n, t^(2*j+1)/(2*j+1)) + 2*t^(2*n+1)/(1-t^2) := by
  have h₁ := Real.sum_range_le_log_div ht ht1 n
  have h₂ := Real.log_div_le_sum_range_add ht ht1 n
  constructor
  · linarith
  · calc
      _ ≤ 2*((∑ j ∈ range n, t^(2*j+1)/(2*j+1)) + t^(2*n+1)/(1-t^2)) := by linarith
      _ = _ := by ring

/-- Exact rational counterpart; evaluation never calls a transcendental function. -/
def atanRat (n : ℕ) (q : ℚ) : ℚ :=
  ∑ j ∈ range n, (-1 : ℚ)^j * q^(2*j+1)/(2*j+1)

def logRat (n : ℕ) (t : ℚ) : ℚ :=
  2 * ∑ j ∈ range n, t^(2*j+1)/(2*j+1)

theorem atanRat_cast (n : ℕ) (q : ℚ) :
    (atanRat n q : ℝ) = atanPoly n (q : ℝ) := by
  simp [atanRat, atanPoly]

theorem logRat_enclosure (n : ℕ) (q : ℚ) (hq : 1 ≤ q) :
    let t := (q-1)/(q+1)
    (logRat n t : ℝ) ≤ Real.log (q : ℝ) ∧
    Real.log (q : ℝ) ≤ ((logRat n t + 2*t^(2*n+1)/(1-t^2) : ℚ) : ℝ) := by
  dsimp
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hden : (0:ℝ) < (q:ℝ)+1 := by linarith
  have ht : 0 ≤ ((q:ℝ)-1)/((q:ℝ)+1) := div_nonneg (by linarith) hden.le
  have ht1 : ((q:ℝ)-1)/((q:ℝ)+1) < 1 := (div_lt_one hden).mpr (by linarith)
  have he : (1+((q:ℝ)-1)/((q:ℝ)+1))/(1-((q:ℝ)-1)/((q:ℝ)+1)) = q := by
    field_simp
    <;> ring
  have h := log_enclosure n _ ht ht1
  rw [he] at h
  simpa [logRat] using h

theorem atanRat_enclosure (n : ℕ) (q : ℚ) :
    ((atanRat n q - |q|^(2*n+1) : ℚ) : ℝ) ≤ Real.arctan (q : ℝ) ∧
    Real.arctan (q : ℝ) ≤ ((atanRat n q + |q|^(2*n+1) : ℚ) : ℝ) := by
  have h := abs_le.mp (atan_remainder_bound n (q : ℝ))
  rw [← atanRat_cast] at h
  push_cast
  constructor <;> linarith

theorem atan_reduce_quarter (x : ℝ) (hx : 0 ≤ x) :
    Real.arctan x = Real.pi/4 + Real.arctan ((x-1)/(x+1)) := by
  have hd : 0 < x+1 := by linarith
  have ht : (1:ℝ) * ((x-1)/(x+1)) < 1 := by
    rw [one_mul]; exact (div_lt_one hd).mpr (by linarith)
  have h := Real.arctan_add ht
  rw [Real.arctan_one] at h
  have he : (1+(x-1)/(x+1))/(1-1*((x-1)/(x+1))) = x := by
    field_simp
    <;> ring
  rw [he] at h
  exact h.symm

theorem atan_reduce_inverse (x : ℝ) (hx : 0 < x) :
    Real.arctan x = Real.pi/2 - Real.arctan x⁻¹ := by
  rw [Real.arctan_inv_of_pos hx]
  ring

/-- Machin's identity transports four rational endpoints to a pi enclosure. -/
theorem pi_enclosure (a b c d : ℚ)
    (ha : (a:ℝ) ≤ Real.arctan (1/5)) (hb : Real.arctan (1/5) ≤ (b:ℝ))
    (hc : (c:ℝ) ≤ Real.arctan (1/239)) (hd : Real.arctan (1/239) ≤ (d:ℝ)) :
    ((16*a-4*d:ℚ):ℝ) ≤ Real.pi ∧ Real.pi ≤ ((16*b-4*c:ℚ):ℝ) := by
  have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num only [inv_eq_one_div] at h
  push_cast
  constructor <;> linarith

theorem log_rat_check (n : ℕ) (q lo hi : ℚ) (hq : 1 ≤ q)
    (hlo : lo ≤ logRat n ((q-1)/(q+1)))
    (hhi : logRat n ((q-1)/(q+1)) +
      2*((q-1)/(q+1))^(2*n+1)/(1-((q-1)/(q+1))^2) ≤ hi) :
    (lo:ℝ) ≤ Real.log (q:ℝ) ∧ Real.log (q:ℝ) ≤ (hi:ℝ) := by
  have h := logRat_enclosure n q hq
  constructor
  · exact le_trans (by exact_mod_cast hlo) h.1
  · exact le_trans h.2 (by exact_mod_cast hhi)

theorem atan_rat_check (n : ℕ) (q lo hi : ℚ)
    (hlo : lo ≤ atanRat n q - |q|^(2*n+1))
    (hhi : atanRat n q + |q|^(2*n+1) ≤ hi) :
    (lo:ℝ) ≤ Real.arctan (q:ℝ) ∧ Real.arctan (q:ℝ) ≤ (hi:ℝ) := by
  have h := atanRat_enclosure n q
  constructor
  · exact le_trans (by exact_mod_cast hlo) h.1
  · exact le_trans h.2 (by exact_mod_cast hhi)

/-- Exact power-of-two range reduction, including negative exponents. -/
theorem log_range_reduction (u : ℝ) (hu : 0 < u) (e : ℤ) :
    Real.log ((2:ℝ)^e*u) = (e:ℝ)*Real.log 2+Real.log u := by
  rw [Real.log_mul (zpow_ne_zero _ (by norm_num)) hu.ne', Real.log_zpow]

/-- Inversion permits the same positive-log enclosure to handle arguments below one. -/
theorem log_inverse_enclosure (x lo hi : ℝ) (hlo : lo ≤ Real.log x⁻¹)
    (hhi : Real.log x⁻¹ ≤ hi) : -hi ≤ Real.log x ∧ Real.log x ≤ -lo := by
  rw [Real.log_inv] at hlo hhi
  constructor <;> linarith

end OddZeta.FourValue.Transcendental

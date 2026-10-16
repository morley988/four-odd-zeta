import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Geometric inequalities for the bounded-root block basis and cell enclosure.
These are uniform lemmas, independent of the finite numerical grid. -/
namespace OddZeta.FourValue.Geometry

theorem power_difference_bound (u v : ℂ) (m : ℕ) :
    ‖u ^ m - v ^ m‖ ≤ 2 * (max ‖u‖ ‖v‖) ^ m := by
  calc
    _ ≤ ‖u ^ m‖ + ‖v ^ m‖ := norm_sub_le _ _
    _ = ‖u‖ ^ m + ‖v‖ ^ m := by rw [norm_pow, norm_pow]
    _ ≤ (max ‖u‖ ‖v‖) ^ m + (max ‖u‖ ‖v‖) ^ m := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = _ := by ring

theorem block_root_distance (z center : ℂ) (delta : ℝ) (hd : 0 ≤ delta)
    (m : ℕ) (hm : m ≠ 0)
    (hroot : (z-center)^m - (delta : ℂ)^m = 0) :
    ‖z-center‖ = delta := by
  have h := congrArg norm (sub_eq_zero.mp hroot)
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd] at h
  exact (pow_left_inj₀ (norm_nonneg _) hd hm).mp h

theorem block_root_bound (z center : ℂ) (delta R : ℝ) (hd : 0 ≤ delta)
    (m : ℕ) (hm : m ≠ 0)
    (hroot : (z-center)^m - (delta : ℂ)^m = 0)
    (hcenter : ‖center‖ + delta ≤ R) : ‖z‖ ≤ R := by
  have h := block_root_distance z center delta hd m hm hroot
  calc
    ‖z‖ = ‖(z-center)+center‖ := by congr 1; ring
    _ ≤ ‖z-center‖+‖center‖ := norm_add_le _ _
    _ ≤ R := by rw [h]; linarith

theorem norm_convex_combination_le_max (z w : ℂ) (t : ℝ)
    (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ‖((1-t : ℝ) : ℂ)*z + (t : ℂ)*w‖ ≤ max ‖z‖ ‖w‖ := by
  have h1t : 0 ≤ 1-t := by linarith
  calc
    _ ≤ ‖((1-t : ℝ) : ℂ)*z‖ + ‖(t : ℂ)*w‖ := norm_add_le _ _
    _ = (1-t)*‖z‖+t*‖w‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg h0, abs_of_nonneg h1t]
    _ ≤ (1-t)*max ‖z‖ ‖w‖+t*max ‖z‖ ‖w‖ := by
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h1t)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) h0)
    _ = _ := by ring

/-- Exact quadratic interpolation identity on a real parameter interval. -/
theorem quadratic_interpolation_identity (a b c : ℂ) (l h t : ℝ) :
    (a * (((1-t)*l+t*h : ℝ) : ℂ)^2 + b * (((1-t)*l+t*h : ℝ) : ℂ) + c) -
      (((1-t : ℝ) : ℂ)*(a*(l:ℂ)^2+b*(l:ℂ)+c) +
       (t:ℂ)*(a*(h:ℂ)^2+b*(h:ℂ)+c)) =
      -a * ((t*(1-t)*(h-l)^2 : ℝ) : ℂ) := by
  push_cast
  ring

theorem quadratic_interpolation_error (a b c : ℂ) (l h t : ℝ)
    (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ‖(a * (((1-t)*l+t*h : ℝ) : ℂ)^2 + b * (((1-t)*l+t*h : ℝ) : ℂ) + c) -
      (((1-t : ℝ) : ℂ)*(a*(l:ℂ)^2+b*(l:ℂ)+c) +
       (t:ℂ)*(a*(h:ℂ)^2+b*(h:ℂ)+c))‖ ≤ ‖a‖ * (h-l)^2 / 4 := by
  rw [quadratic_interpolation_identity, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ t*(1-t)*(h-l)^2)]
  have ht : t*(1-t) ≤ 1/4 := by nlinarith [sq_nonneg (t-1/2)]
  have hs : t*(1-t)*(h-l)^2 ≤ (h-l)^2/4 := by
    nlinarith [mul_le_mul_of_nonneg_right ht (sq_nonneg (h-l))]
  nlinarith [mul_le_mul_of_nonneg_left hs (norm_nonneg a)]

/-- Combining an interpolation error with endpoint distance bounds. -/
theorem distance_enclosure (z zl zh center : ℂ) (t e : ℝ)
    (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (herr : ‖z - (((1-t : ℝ):ℂ)*zl + (t:ℂ)*zh)‖ ≤ e) :
    ‖z-center‖ ≤ max ‖zl-center‖ ‖zh-center‖ + e := by
  have hconv := norm_convex_combination_le_max (zl-center) (zh-center) t h0 h1
  have hid : z-center = (z-(((1-t:ℝ):ℂ)*zl+(t:ℂ)*zh)) +
      (((1-t:ℝ):ℂ)*(zl-center)+(t:ℂ)*(zh-center)) := by
    push_cast; ring
  rw [hid]
  exact (norm_add_le _ _).trans (by linarith)

#print axioms power_difference_bound
#print axioms block_root_bound
#print axioms quadratic_interpolation_error
#print axioms distance_enclosure

end OddZeta.FourValue.Geometry

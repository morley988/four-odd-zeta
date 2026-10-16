import FourValueCertificatePotential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

noncomputable section
namespace OddZeta.FourValue.Transcendental
open Set Finset

def curveJ (a y : ℝ) : ℝ := certificateJ (1+(3/5)*y+a) y

def curveH (a y : ℝ) : ℝ := curveJ a y - curveJ (-a) y

def curveQ (a y : ℝ) : ℝ := (1+(3/5)*y+a)^2+y^2

theorem curveJ_deriv (a y : ℝ) (hy : 0 < y) :
    HasDerivAt (curveJ a)
      ((3/10)*Real.log (curveQ a y) + Real.arctan ((1+(3/5)*y+a)/y)) y := by
  have hu : HasDerivAt (fun t : ℝ => 1+(3/5)*t+a) (3/5) y := by
    convert! (((hasDerivAt_id y).const_mul (3/5)).const_add 1).add_const a using 1 <;> ring
  have hq : curveQ a y ≠ 0 := ne_of_gt (by
    dsimp [curveQ]; nlinarith [sq_nonneg (1+(3/5)*y+a), sq_pos_of_pos hy])
  have hl := ((hu.pow 2).add ((hasDerivAt_id y).pow 2)).log hq
  have ha := (hu.div (hasDerivAt_id y) hy.ne').arctan
  have h := (((hu.div_const 2).mul hl).sub hu).add ((hasDerivAt_id y).mul ha)
  convert! h using 1
  dsimp [curveQ]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq]
  field_simp
  <;> ring

theorem curveH_deriv (a y : ℝ) (hy : 0 < y) :
    HasDerivAt (curveH a)
      ((3/10)*(Real.log (curveQ a y)-Real.log (curveQ (-a) y)) +
        (Real.arctan ((1+(3/5)*y+a)/y)-Real.arctan ((1+(3/5)*y-a)/y))) y := by
  convert! (curveJ_deriv a y hy).sub (curveJ_deriv (-a) y hy) using 1
  simp only [sub_eq_add_neg]
  ring

def curveHPrime (a y : ℝ) : ℝ :=
  (3/10)*(Real.log (curveQ a y)-Real.log (curveQ (-a) y)) +
    (Real.arctan ((1+(3/5)*y+a)/y)-Real.arctan ((1+(3/5)*y-a)/y))

theorem curveQ_pos (a y : ℝ) (hy : 0 < y) : 0 < curveQ a y := by
  dsimp [curveQ]
  nlinarith [sq_nonneg (1+(3/5)*y+a), sq_pos_of_pos hy]

theorem curveHPrime_nonneg (a y : ℝ) (ha : 0 ≤ a) (hy : 0 < y) :
    0 ≤ curveHPrime a y := by
  have hq : curveQ (-a) y ≤ curveQ a y := by
    dsimp [curveQ]; nlinarith [mul_nonneg ha hy.le]
  have hl := Real.log_le_log (curveQ_pos (-a) y hy) hq
  have ht : (1+(3/5)*y-a)/y ≤ (1+(3/5)*y+a)/y := by
    apply div_le_div_of_nonneg_right _ hy.le; linarith
  have hat := Real.arctan_le_arctan_iff.mpr ht
  dsimp [curveHPrime]
  linarith

theorem curveQ_ratio (a y : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hy : 0 < y) :
    curveQ a y / curveQ (-a) y ≤ ((1+a)/(1-a))^2 := by
  have hminus : 0 < 1-a := by linarith
  rw [div_pow, div_le_div_iff₀ (curveQ_pos (-a) y hy) (sq_pos_of_pos hminus)]
  have hid : (1+a)^2*curveQ (-a) y-curveQ a y*(1-a)^2 =
      4*a*((3/5*y)*(1+(3/5)*y-a^2)+y^2) := by dsimp [curveQ]; ring
  have ha2 : a^2 ≤ 1 := by nlinarith
  have hn : 0 ≤ 4*a*((3/5*y)*(1+(3/5)*y-a^2)+y^2) := by
    apply mul_nonneg (by positivity)
    apply add_nonneg _ (sq_nonneg _)
    apply mul_nonneg (by positivity)
    nlinarith
  linarith

theorem curveHPrime_upper (a y : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hy : 0 < y) :
    curveHPrime a y ≤ (3/5)*Real.log ((1+a)/(1-a))+Real.pi/2 := by
  have hlog := Real.log_le_log (div_pos (curveQ_pos a y hy) (curveQ_pos (-a) y hy))
    (curveQ_ratio a y ha ha1 hy)
  rw [Real.log_div (curveQ_pos a y hy).ne' (curveQ_pos (-a) y hy).ne', Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hat := Real.arctan_lt_pi_div_two ((1+(3/5)*y+a)/y)
  have hat0 : 0 ≤ Real.arctan ((1+(3/5)*y-a)/y) := by
    apply Real.arctan_nonneg.mpr
    apply div_nonneg _ hy.le
    linarith
  dsimp [curveHPrime]
  linarith

def cellSlope : ℝ :=
  (3/5)*∑ i : Fin 15, Real.log ((1+targetAlpha i)/(1-targetAlpha i)) + 19*Real.pi/2

def gPrime (y : ℝ) : ℝ :=
  5*curveHPrime 1 y - ∑ i : Fin 15, curveHPrime (targetAlpha i) y - 2*Real.pi

theorem certificateG_deriv (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t => certificateG t-2*Real.pi*t) (gPrime y) y := by
  have hs := HasDerivAt.sum (u := Finset.univ)
    (fun i _ => curveH_deriv (targetAlpha i) y hy)
  have h := (((curveH_deriv 1 y hy).const_mul 5).const_add targetNormalizationEntropy).sub hs
  have h' := h.sub ((hasDerivAt_id y).const_mul (2*Real.pi))
  convert! h' using 1
  simp only [gPrime, curveHPrime, mul_one]

theorem gPrime_lower (y : ℝ) (hy : 0 < y) : -cellSlope ≤ gPrime y := by
  have hn := curveHPrime_nonneg 1 y (by norm_num) hy
  have hs : (∑ i : Fin 15, curveHPrime (targetAlpha i) y) ≤
      ∑ i : Fin 15, ((3/5)*Real.log ((1+targetAlpha i)/(1-targetAlpha i))+Real.pi/2) := by
    apply sum_le_sum
    intro i _
    exact curveHPrime_upper _ _ (targetAlpha_bounds i).1
      (by linarith [(targetAlpha_bounds i).2]) hy
  rw [sum_add_distrib, ← mul_sum] at hs
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  dsimp [cellSlope, gPrime]
  linarith

theorem cellSlope_nonneg : 0 ≤ cellSlope := by
  have hs : 0 ≤ ∑ i : Fin 15, Real.log ((1+targetAlpha i)/(1-targetAlpha i)) := by
    apply sum_nonneg
    intro i _
    apply Real.log_nonneg
    apply (one_le_div (by linarith [(targetAlpha_bounds i).2])).mpr
    linarith [(targetAlpha_bounds i).1]
  dsimp [cellSlope]
  positivity

/-- The exact slope allowance used in the recovered certificate covers the whole cell. -/
theorem certificateG_cell (y h δ : ℝ) (hy : 0 < y) (hyh : y ≤ h) (hh : h-y ≤ δ) :
    certificateG y-2*Real.pi*y ≤ certificateG h-2*Real.pi*h+cellSlope*δ := by
  let f := fun t => certificateG t-2*Real.pi*t+cellSlope*t
  have hd : ∀ t ∈ Icc y h, HasDerivAt f (gPrime t+cellSlope) t := by
    intro t ht
    convert! (certificateG_deriv t (lt_of_lt_of_le hy ht.1)).add
      ((hasDerivAt_id t).const_mul cellSlope) using 1 <;> simp [f]
  have hm : MonotoneOn f (Icc y h) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc y h)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have ht' := interior_subset ht
    have hg := gPrime_lower t (lt_of_lt_of_le hy ht'.1)
    linarith
  have he := hm (left_mem_Icc.mpr hyh) (right_mem_Icc.mpr hyh) hyh
  have hb := mul_le_mul_of_nonneg_left hh cellSlope_nonneg
  dsimp [f] at he
  nlinarith

end OddZeta.FourValue.Transcendental

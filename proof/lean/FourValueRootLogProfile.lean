import FourValueConcreteContourComplete
import Mathlib.Analysis.SumIntegralComparisons

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory Set

def rootLogProfile (z : ℂ) (t : ℝ) : ℝ := Real.log ‖z-(t:ℂ)‖

theorem rootLogProfile_norm_pos (z : ℂ) (t : ℝ) (ht : t<z.re) : 0<‖z-(t:ℂ)‖ := by
  apply norm_pos_iff.mpr
  intro h
  have he := congrArg Complex.re (sub_eq_zero.mp h)
  simp only [Complex.ofReal_re] at he
  linarith

theorem rootLogProfile_antitone (z : ℂ) (a b : ℝ) (hb : b<z.re) :
    AntitoneOn (rootLogProfile z) (Icc a b) := by
  intro x hx y hy hxy
  apply Real.log_le_log (rootLogProfile_norm_pos z y (lt_of_le_of_lt hy.2 hb))
  have hnx := Complex.sq_norm (z-(x:ℂ))
  have hny := Complex.sq_norm (z-(y:ℂ))
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at hnx hny
  nlinarith [norm_nonneg (z-(x:ℂ)),norm_nonneg (z-(y:ℂ)),mul_nonneg (sub_nonneg.mpr hxy)
    (show 0≤2*z.re-x-y by linarith [hy.2])]

theorem antitone_grid_sum_error (f : ℝ→ℝ) (a : ℝ) (N : ℕ)
    (hf : AntitoneOn f (Icc a (a+N))) :
    f (a+N)≤(∑ j∈Finset.range (N+1),f (a+j))-(∫ x in a..a+N,f x) ∧
    (∑ j∈Finset.range (N+1),f (a+j))-(∫ x in a..a+N,f x)≤f a := by
  have hl := hf.integral_le_sum
  have hu := hf.sum_le_integral
  constructor
  · rw [Finset.sum_range_succ]
    linarith
  · have he := Finset.sum_range_succ' (fun j : ℕ => f (a+j)) N
    rw [he]
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero] at hu ⊢
    linarith

theorem centeredRoot_log_sum (a : ℕ) (z : ℂ) (hz : (a:ℝ)<z.re) :
    Real.log ‖(centeredDenominator (K:=ℂ) a).eval z‖=
      ∑ j∈poleWindow a,rootLogProfile z (j:ℝ) := by
  rw [centeredDenominator_integerProduct,integerRootProduct,Polynomial.eval_prod,norm_prod]
  rw [Real.log_prod]
  · simp only [eval_sub,eval_X,eval_C,rootLogProfile,Complex.ofReal_intCast]
  · intro j hj
    simp only [eval_sub,eval_X,eval_C]
    apply norm_ne_zero_iff.mpr
    intro he
    have hr := congrArg Complex.re (sub_eq_zero.mp he)
    simp only [Complex.intCast_re] at hr
    have hj' : (j:ℝ)≤a := by exact_mod_cast (Finset.mem_Icc.mp hj).2
    linarith

theorem centeredRoot_log_grid (a : ℕ) (z : ℂ) :
    (∑ j∈poleWindow a,rootLogProfile z (j:ℝ))=
      ∑ j∈Finset.range (2*a+1),rootLogProfile z (-(a:ℝ)+(j:ℝ)) := by
  symm
  apply Finset.sum_bij (fun (j : ℕ) _ => (j:ℤ)-(a:ℤ))
  · intro j hj
    simp only [poleWindow,Finset.mem_Icc]
    have hj' := Finset.mem_range.mp hj
    omega
  · intro j hj l hl he
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    refine ⟨(j+(a:ℤ)).toNat,?_,?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro j hj
    congr 1
    push_cast
    ring

theorem centeredRoot_log_integral_error (a : ℕ) (z : ℂ) (hz : (a:ℝ)<z.re) :
    rootLogProfile z a≤Real.log ‖(centeredDenominator (K:=ℂ) a).eval z‖-
        (∫ t in -(a:ℝ)..(a:ℝ),rootLogProfile z t) ∧
    Real.log ‖(centeredDenominator (K:=ℂ) a).eval z‖-
        (∫ t in -(a:ℝ)..(a:ℝ),rootLogProfile z t)≤rootLogProfile z (-(a:ℝ)) := by
  have h := antitone_grid_sum_error (rootLogProfile z) (-(a:ℝ)) (2*a)
    (by convert rootLogProfile_antitone z (-(a:ℝ)) (a:ℝ) hz using 1 <;> push_cast <;> ring)
  rw [centeredRoot_log_sum a z hz,centeredRoot_log_grid]
  convert h using 1 <;> push_cast <;> ring
end OddZeta.FourValue

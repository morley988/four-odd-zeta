import FourValueNormalizationLog
import FourValueScaledRootIntegral

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory Set

def targetAlpha (i : Fin 15) : ℝ := (targetEndpointTuple 1 i:ℝ)/100

def targetWeightPotential (z : ℂ) : ℝ := targetNormalizationEntropy+
  5*rootLogIntegral z 1-∑ i : Fin 15,rootLogIntegral z (targetAlpha i)

theorem targetAlpha_bounds (i : Fin 15) : 0≤targetAlpha i ∧ targetAlpha i≤67/100 := by
  unfold targetAlpha
  have h := targetEndpointTuple_le_67 1 i
  constructor
  · positivity
  · have hc : (targetEndpointTuple 1 i:ℝ)≤67 := by exact_mod_cast h
    linarith

theorem targetEndpointTuple_scaled (n : ℕ) (i : Fin 15) :
    (targetEndpointTuple n i:ℝ)=(100*(n:ℝ))*targetAlpha i := by
  fin_cases i <;> norm_num [targetEndpointTuple,targetAlpha] <;> ring

theorem targetEndpointTuple_sum (n : ℕ) : ∑ i : Fin 15,(targetEndpointTuple n i:ℝ)=861*(n:ℝ) := by
  norm_num [targetEndpointTuple,Fin.sum_univ_succ]
  ring

theorem centeredDenominator_eval_ne_zero_re (a : ℕ) (z : ℂ) (hz : (a:ℝ)<z.re) :
    (centeredDenominator (K:=ℂ) a).eval z≠0 := by
  rw [centeredDenominator_integerProduct,integerRootProduct,Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simp only [eval_sub,eval_X,eval_C]
  intro he
  have hr := congrArg Complex.re (sub_eq_zero.mp he)
  simp only [Complex.intCast_re] at hr
  have hj' : (j:ℝ)≤a := by exact_mod_cast (Finset.mem_Icc.mp hj).2
  linarith

theorem analyticWeight_log_identity (n : ℕ) (z : ℂ) (hz : (100*(n:ℝ))<z.re) :
    Real.log ‖analyticZetaFunction n 1 z‖=Real.log ‖targetNormalization (K:=ℂ) n‖+
      Real.log 2+Real.log ‖z‖+5*Real.log ‖(centeredDenominator (K:=ℂ) (100*n)).eval z‖-
      ∑ i : Fin 15,Real.log ‖(centeredDenominator (K:=ℂ) (targetEndpointTuple n i)).eval z‖ := by
  have hmain := centeredDenominator_eval_ne_zero_re (100*n) z (by simpa using hz)
  have hi (i : Fin 15) := centeredDenominator_eval_ne_zero_re (targetEndpointTuple n i) z
    (lt_of_le_of_lt (by exact_mod_cast targetEndpointTuple_bounded n i) hz)
  have hz0 : z≠0 := by intro he; simp [he] at hz; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hp0 := norm_pos_iff.mpr hz0
  have hp1 := norm_pos_iff.mpr hmain
  have hp2 := norm_pos_iff.mpr (targetNormalization_ne_zero (K:=ℂ) n)
  rw [analyticZetaFunction_formula]
  simp only [eval_one,mul_one,norm_div,norm_mul,norm_pow,norm_prod,Complex.norm_ofNat]
  rw [Real.log_div (by positivity) (Finset.prod_ne_zero_iff.mpr (fun i _ => norm_ne_zero_iff.mpr (hi i))),
    Real.log_mul (norm_ne_zero_iff.mpr (targetNormalization_ne_zero n)) (by positivity),
    Real.log_mul (by positivity) (pow_ne_zero 5 (norm_ne_zero_iff.mpr hmain)),
    Real.log_mul (by norm_num) (norm_ne_zero_iff.mpr hz0),Real.log_pow,
    Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (hi i))]
  ring
end OddZeta.FourValue

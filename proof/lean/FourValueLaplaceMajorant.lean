import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section
namespace OddZeta.FourValue
open MeasureTheory Set

theorem polynomial_exp_integrable (k : ℕ) (b : ℝ) (hb : 0<b) :
    IntegrableOn (fun y : ℝ => (1+y)^k*Real.exp (-b*y)) (Ioi 0) := by
  have hp (j : ℕ) : IntegrableOn (fun y : ℝ => y^j*Real.exp (-b*y)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s:=(j:ℝ)) (p:=1) (b:=b)
      (by have := Nat.cast_nonneg (α:=ℝ) j; linarith) (by norm_num) hb
    simpa only [Real.rpow_natCast,Real.rpow_one] using h
  have hs := integrable_finsetSum (Finset.range (k+1)) (fun j _ => (hp j).const_mul (Nat.choose k j:ℝ))
  apply IntegrableOn.congr_fun hs _ measurableSet_Ioi
  intro y hy
  dsimp only
  rw [add_comm (1:ℝ) y,add_pow,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [one_pow,mul_one]
  ring
end OddZeta.FourValue

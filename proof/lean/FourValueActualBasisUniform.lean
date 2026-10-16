import FourValueShiftedBasisBound
import FourValueTransferPolynomialBound

noncomputable section
namespace OddZeta.FourValue
open Polynomial

theorem upperContourRay_scaled (n : ℕ) (hn : 1≤n) (y : ℝ) :
    upperContourRay n (100*(n:ℝ)*y)=
      (100*(n:ℂ))*(normalizedContourPoint y+(1/(2*(100*(n:ℝ))):ℝ)) := by
  have hn0 : (n:ℂ)≠0 := by exact_mod_cast (show n≠0 by omega)
  unfold upperContourRay baseContourRay normalizedContourPoint
  push_cast
  field_simp
  <;> ring

theorem actualAdaptedBasis_uniform_log_bound (n i : ℕ) (hn : 1≤n) (hi : i≤targetHankelDegree n)
    (y : ℝ) (hy : 0≤y)
    (hz : (actualAdaptedBasis n i).eval ((upperContourRay n (100*(n:ℝ)*y))^2)≠0) :
    2*Real.log ‖(actualAdaptedBasis n i).eval ((upperContourRay n (100*(n:ℝ)*y))^2)‖≤
      4*(i:ℝ)*Real.log (100*(n:ℝ))-2*Real.log (Nat.factorial (2*i):ℝ)+
      (i:ℝ)*analyticBasisPotential (adaptedWeights n i) ((normalizedContourPoint y)^2)+
      90*Real.log 4+90*Real.log 2500+180*Real.log 5+360*Real.log (1+y)+500 := by
  have hM : (1:ℝ)≤100*(n:ℝ) := by exact_mod_cast (show 1≤100*n by omega)
  have hiM : (i:ℝ)≤2*(100*(n:ℝ)) := by
    have h : targetHankelDegree n≤181*n := by unfold targetHankelDegree; omega
    have hc : (i:ℝ)≤181*(n:ℝ) := by exact_mod_cast le_trans hi h
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  have he : ((upperContourRay n (100*(n:ℝ)*y))^2)=
      ((100*(n:ℝ):ℝ):ℂ)^2*(normalizedContourPoint y+(1/(2*(100*(n:ℝ))):ℝ))^2 := by
    rw [upperContourRay_scaled n hn,mul_pow]
    push_cast
    rfl
  rw [he] at hz ⊢
  unfold actualAdaptedBasis at hz ⊢
  push_cast at hz ⊢
  convert shifted_scaled_basis_log_bound (100*(n:ℝ)) hM i hiM _
    (adaptedWeights_nonneg n i hn hi) (adaptedWeights_sum n i hn hi) y hy (by simpa using hz) using 1 <;> push_cast <;> rfl
end OddZeta.FourValue

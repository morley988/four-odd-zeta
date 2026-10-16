import FourValueRowRiemannLimit
import FourValueUniformMinorBound

noncomputable section
namespace OddZeta.FourValue
open MeasureTheory Set Filter
open scoped Topology

theorem factorialRowRate_continuous : Continuous factorialRowRate := by
  have he : factorialRowRate=fun s : ℝ => -2*((2*s)*Real.log (2*s))+4*s := by
    ext s
    unfold factorialRowRate
    ring
  rw [he]
  exact ((Real.continuous_mul_log.comp (continuous_const.mul continuous_id)).const_mul (-2)).add
    (continuous_const.mul continuous_id)

theorem factorialRowRate_integral (C : ℝ) (hC : 0<C) :
    (∫ s in 0..C,factorialRowRate s)= -2*C^2*Real.log (2*C)+3*C^2 := by
  let F : ℝ→ℝ := fun s => -2*s^2*Real.log (2*s)+3*s^2
  have hc : Continuous F := by
    have he : F=fun s : ℝ => -s*((2*s)*Real.log (2*s))+3*s^2 := by
      ext s
      dsimp [F]
      ring
    rw [he]
    exact (continuous_id.neg.mul (Real.continuous_mul_log.comp (continuous_const.mul continuous_id))).add
      (continuous_const.mul (continuous_id.pow 2))
  have hd (x : ℝ) (hx : x∈Ioo 0 C) : HasDerivAt F (factorialRowRate x) x := by
    have hx0 : x≠0 := ne_of_gt hx.1
    have hlog := ((hasDerivAt_id x).const_mul (2:ℝ)).log (by positivity : 2*x≠0)
    have h := ((((hasDerivAt_id x).pow 2).const_mul (-2)).mul hlog).add
      (((hasDerivAt_id x).pow 2).const_mul 3)
    convert! h using 1
    unfold factorialRowRate
    dsimp only [id_eq,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
    field_simp
    <;> ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hC.le hc.continuousOn hd
    (factorialRowRate_continuous.intervalIntegrable (μ:=volume) 0 C)
  simpa [F] using h

theorem contourRowRate_continuousOn (V : ℝ→ℝ) (hV : ContinuousOn V (Icc 0 basisLimit)) :
    ContinuousOn (contourRowRate V) (Icc 0 basisLimit) :=
  hV.add factorialRowRate_continuous.continuousOn

theorem contourRowRate_integral (V : ℝ→ℝ) (hV : ContinuousOn V (Icc 0 basisLimit)) :
    (∫ s in 0..basisLimit,contourRowRate V s)=
      (∫ s in 0..basisLimit,V s)-2*basisLimit^2*Real.log (2*basisLimit)+3*basisLimit^2 := by
  have hC : 0<basisLimit := by norm_num [basisLimit]
  have hi : IntervalIntegrable V volume 0 basisLimit := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hC.le] using hV
  unfold contourRowRate
  rw [intervalIntegral.integral_add hi (factorialRowRate_continuous.intervalIntegrable _ _),
    factorialRowRate_integral basisLimit hC]
  ring
end OddZeta.FourValue

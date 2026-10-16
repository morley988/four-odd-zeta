import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.Tactic

noncomputable section
namespace OddZeta.FourValue
open scoped UpperHalfPlane

/-- The fifth-order cotangent kernel, with residue normalization 1/4!. -/
def contourKernel (z : ℂ) : ℂ :=
  iteratedDeriv 4 (fun x : ℂ => (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*x)) z / 24

theorem contourKernel_integer_series (z : ℂ) (hz : 0<z.im) :
    contourKernel z=∑' k : ℤ,1/(z+k)^5 := by
  have h := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow (k:=4) (by norm_num) hz
  rw [iteratedDerivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hz] at h
  unfold contourKernel
  rw [h]
  norm_num

theorem contourKernel_q_series (z : ℂ) (hz : 0<z.im) :
    contourKernel z=((-2*(Real.pi:ℂ)*Complex.I)^5/24)*
      ∑' k : ℕ,(k:ℂ)^4*Complex.exp (2*(Real.pi:ℂ)*Complex.I*z)^k := by
  rw [contourKernel_integer_series z hz]
  simpa [Nat.factorial] using EisensteinSeries.qExpansion_identity (k:=4) (by norm_num) ⟨z,hz⟩

def fourthPowerMajorant (ρ : ℝ) : ℝ := ∑' k : ℕ,((k:ℝ)+1)^4*ρ^k

theorem fourthPowerMajorant_summable (ρ : ℝ) (hρ : 0<ρ) (hρ1 : ρ<1) :
    Summable (fun k : ℕ => ((k:ℝ)+1)^4*ρ^k) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one (R:=ℝ) 4
    (show ‖ρ‖<1 by simpa [Real.norm_eq_abs,abs_of_pos hρ] using hρ1)
  have ht := ((summable_nat_add_iff 1).mpr hs).div_const ρ
  apply ht.congr
  intro k
  push_cast
  rw [pow_succ]
  field_simp
  ring

theorem fourthPowerMajorant_nonneg (ρ : ℝ) (hρ : 0≤ρ) : 0≤fourthPowerMajorant ρ := by
  apply tsum_nonneg
  intro k
  positivity

theorem fourthPowerSeries_bound (q : ℂ) (ρ : ℝ) (hρ : 0<ρ) (hρ1 : ρ<1)
    (hq : ‖q‖≤ρ) :
    ‖∑' k : ℕ,(k:ℂ)^4*q^k‖ ≤ fourthPowerMajorant ρ*‖q‖ := by
  have hq1 : ‖q‖<1 := hq.trans_lt hρ1
  have hs := summable_pow_mul_geometric_of_norm_lt_one (R:=ℂ) 4 hq1
  have ht := (fourthPowerMajorant_summable ρ hρ hρ1).mul_right ‖q‖
  rw [← Summable.sum_add_tsum_nat_add 1 hs]
  simp only [Finset.sum_range_one,Nat.cast_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
    zero_mul,zero_add]
  calc
    _ ≤ ∑' k : ℕ, (((k:ℝ)+1)^4*ρ^k)*‖q‖ := by
      apply tsum_of_norm_bounded ht.hasSum
      intro k
      rw [norm_mul,norm_pow,Complex.norm_natCast,norm_pow,pow_succ ‖q‖ k]
      push_cast
      calc
        _ ≤ ((k:ℝ)+1)^4*(ρ^k*‖q‖) := by gcongr
        _ = _ := by ring
    _ = _ := tsum_mul_right

theorem contourKernel_exp_norm (z : ℂ) :
    ‖Complex.exp (2*(Real.pi:ℂ)*Complex.I*z)‖=Real.exp (-2*Real.pi*z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re,Complex.mul_im]

theorem contourKernel_upper_bound (z : ℂ) (hz : 1≤z.im) :
    ‖contourKernel z‖ ≤
      ((2*Real.pi)^5/24*fourthPowerMajorant (Real.exp (-2*Real.pi)))*
        Real.exp (-2*Real.pi*z.im) := by
  have hρ := Real.exp_pos (-2*Real.pi)
  have hρ1 : Real.exp (-2*Real.pi)<1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hq : ‖Complex.exp (2*(Real.pi:ℂ)*Complex.I*z)‖≤Real.exp (-2*Real.pi) := by
    rw [contourKernel_exp_norm,Real.exp_le_exp]
    nlinarith [Real.pi_pos]
  rw [contourKernel_q_series z (by linarith),norm_mul]
  have hc : ‖(-2*(Real.pi:ℂ)*Complex.I)^5/24‖=(2*Real.pi)^5/24 := by
    simp [norm_div,norm_pow,norm_mul,abs_of_pos Real.pi_pos]
  rw [hc]
  have hb := fourthPowerSeries_bound _ _ hρ hρ1 hq
  rw [contourKernel_exp_norm] at hb
  calc
    _ ≤ ((2*Real.pi)^5/24)*(fourthPowerMajorant (Real.exp (-2*Real.pi))*Real.exp (-2*Real.pi*z.im)) := by
      gcongr
    _ = _ := by ring
end OddZeta.FourValue

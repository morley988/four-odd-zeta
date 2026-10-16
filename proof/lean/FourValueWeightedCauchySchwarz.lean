import FourValueAnalyticDeterminants
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
namespace OddZeta.FourValue
open MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem weighted_complex_cauchy_schwarz (a b c : α→ℂ)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ) (hc : AEStronglyMeasurable c μ)
    (hA : Integrable (fun x => ‖a x‖^2*‖c x‖) μ)
    (hB : Integrable (fun x => ‖b x‖^2*‖c x‖) μ) :
    ‖∫ x,a x*b x*c x ∂μ‖≤
      Real.sqrt (∫ x,‖a x‖^2*‖c x‖ ∂μ)*Real.sqrt (∫ x,‖b x‖^2*‖c x‖ ∂μ) := by
  let f : α→ℝ := fun x => ‖a x‖*Real.sqrt ‖c x‖
  let g : α→ℝ := fun x => ‖b x‖*Real.sqrt ‖c x‖
  have hcm : AEStronglyMeasurable (fun x => Real.sqrt ‖c x‖) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hc.norm
  have hf : MemLp f 2 μ := (memLp_two_iff_integrable_sq (ha.norm.mul hcm)).mpr (by
    simpa [f,mul_pow,Real.sq_sqrt] using hA)
  have hg : MemLp g 2 μ := (memLp_two_iff_integrable_sq (hb.norm.mul hcm)).mpr (by
    simpa [g,mul_pow,Real.sq_sqrt] using hB)
  have hfg : Integrable (fun x => f x*g x) μ := by
    exact memLp_one_iff_integrable.mp (hg.mul hf : MemLp (fun x => f x*g x) 1 μ)
  have hnorm : ∀ x,‖a x*b x*c x‖=f x*g x := by
    intro x
    dsimp [f,g]
    rw [norm_mul,norm_mul]
    calc
      _ = ‖a x‖*‖b x‖*(Real.sqrt ‖c x‖)^2 := by rw [Real.sq_sqrt (norm_nonneg _)]
      _ = _ := by ring
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (p:=2) (q:=2)
    (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall (fun x => show 0≤f x by dsimp [f]; positivity))
    (Filter.Eventually.of_forall (fun x => show 0≤g x by dsimp [g]; positivity))
    (by simpa using hf) (by simpa using hg)
  have hAeq : (∫ x,(f x)^(2:ℝ) ∂μ)=∫ x,‖a x‖^2*‖c x‖ ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by simp [f,Real.rpow_two,mul_pow,Real.sq_sqrt])
  have hBeq : (∫ x,(g x)^(2:ℝ) ∂μ)=∫ x,‖b x‖^2*‖c x‖ ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by simp [g,Real.rpow_two,mul_pow,Real.sq_sqrt])
  rw [hAeq,hBeq,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow] at hCS
  apply le_trans (norm_integral_le_of_norm_le hfg (Filter.Eventually.of_forall (fun x => (hnorm x).le))) hCS

theorem two_term_sqrt_cauchy_schwarz (a b c d : ℝ) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) :
    Real.sqrt a*Real.sqrt b+Real.sqrt c*Real.sqrt d≤Real.sqrt (a+c)*Real.sqrt (b+d) := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := Real.sq_sqrt hc
  have h4 := Real.sq_sqrt hd
  have h5 := Real.sq_sqrt (add_nonneg ha hc)
  have h6 := Real.sq_sqrt (add_nonneg hb hd)
  have h7 := sq_nonneg (Real.sqrt a*Real.sqrt d-Real.sqrt c*Real.sqrt b)
  have hnon : 0≤Real.sqrt (a+c)*Real.sqrt (b+d) := by positivity
  have hs : (Real.sqrt a*Real.sqrt b+Real.sqrt c*Real.sqrt d)^2 ≤
      (Real.sqrt (a+c)*Real.sqrt (b+d))^2 := by
    calc
      _ ≤ (a+c)*(b+d) := by
        nlinarith [sq_nonneg (Real.sqrt a*Real.sqrt d-Real.sqrt c*Real.sqrt b),
          mul_self_nonneg (Real.sqrt a*Real.sqrt b)]
      _ = _ := by rw [mul_pow,h5,h6]
  nlinarith [sq_nonneg (Real.sqrt (a+c)*Real.sqrt (b+d) -
    (Real.sqrt a*Real.sqrt b+Real.sqrt c*Real.sqrt d))]
end OddZeta.FourValue

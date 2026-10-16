import FourValueWeightedCauchySchwarz
import FourValueActualAdaptedBasis
import FourValueContourConvergence

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory

def analyticContourWeight (n : ℕ) (z : ℂ) : ℂ :=
  analyticZetaFunction n 1 z*contourKernel z

def contourRayEnergy (n : ℕ) (P : ℂ[X]) (γ : ℝ→ℂ) : ℝ :=
  ∫ t in Set.Ioi (0:ℝ), ‖P.eval ((γ t)^2)‖^2*‖analyticContourWeight n (γ t)‖

theorem analyticZetaFunction_mul (n : ℕ) (P Q : ℂ[X]) (z : ℂ) :
    analyticZetaFunction n (P*Q) z*contourKernel z=
      P.eval (z^2)*Q.eval (z^2)*analyticContourWeight n z := by
  simp only [analyticContourWeight,analyticZetaFunction_formula,eval_mul,eval_one]
  ring

theorem contourRayEnergy_nonneg (n : ℕ) (P : ℂ[X]) (γ : ℝ→ℂ) :
    0≤contourRayEnergy n P γ := by
  apply integral_nonneg
  intro t
  positivity

theorem contourRayEnergy_integrable (n : ℕ) (P : ℂ[X]) (γ : ℝ→ℂ)
    (h : IntegrableOn (fun t => analyticZetaFunction n (P*P) (γ t)*contourKernel (γ t)) (Set.Ioi 0)) :
    IntegrableOn (fun t => ‖P.eval ((γ t)^2)‖^2*‖analyticContourWeight n (γ t)‖) (Set.Ioi 0) := by
  have he : (fun t => ‖analyticZetaFunction n (P*P) (γ t)*contourKernel (γ t)‖)=
      (fun t => ‖P.eval ((γ t)^2)‖^2*‖analyticContourWeight n (γ t)‖) := by
    funext t
    simp only [analyticZetaFunction_mul,norm_mul,pow_two]
  have hh := h.norm
  rw [he] at hh
  exact hh

theorem analyticContourWeight_continuousOn (n : ℕ) (γ : ℝ→ℂ) (hγ : Continuous γ)
    (hre : ∀ t : ℝ,0<t → ((67*n:ℕ):ℝ)<(γ t).re)
    (hreg : ∀ t : ℝ,0<t → γ t∈Complex.integerComplement) :
    ContinuousOn (fun t => analyticContourWeight n (γ t)) (Set.Ioi 0) :=
  ((analyticZetaFunction_continuousOn n 1).comp hγ.continuousOn hre).mul
    (contourKernel_continuousOn.comp hγ.continuousOn hreg)

theorem contourRay_bilinear_bound (n : ℕ) (P Q : ℂ[X]) (γ : ℝ→ℂ) (hγ : Continuous γ)
    (hc : ContinuousOn (fun t => analyticContourWeight n (γ t)) (Set.Ioi 0))
    (hP : IntegrableOn (fun t => analyticZetaFunction n (P*P) (γ t)*contourKernel (γ t)) (Set.Ioi 0))
    (hQ : IntegrableOn (fun t => analyticZetaFunction n (Q*Q) (γ t)*contourKernel (γ t)) (Set.Ioi 0)) :
    ‖∫ t in Set.Ioi (0:ℝ),analyticZetaFunction n (P*Q) (γ t)*contourKernel (γ t)‖≤
      Real.sqrt (contourRayEnergy n P γ)*Real.sqrt (contourRayEnergy n Q γ) := by
  simp_rw [analyticZetaFunction_mul]
  apply weighted_complex_cauchy_schwarz
  · exact ((P.continuous.comp (hγ.pow 2)).aestronglyMeasurable)
  · exact ((Q.continuous.comp (hγ.pow 2)).aestronglyMeasurable)
  · exact hc.aestronglyMeasurable measurableSet_Ioi
  · exact contourRayEnergy_integrable n P γ hP
  · exact contourRayEnergy_integrable n Q γ hQ

theorem upperContourWeight_continuousOn (n : ℕ) :
    ContinuousOn (fun t => analyticContourWeight n (upperContourRay n t)) (Set.Ioi 0) := by
  apply analyticContourWeight_continuousOn n _ (by unfold upperContourRay baseContourRay; fun_prop)
  · intro t ht
    rw [upperContourRay_re]
    have : ((67*n:ℕ):ℝ)≤(100*n:ℕ) := by exact_mod_cast (show 67*n≤100*n by omega)
    linarith
  · exact fun t ht => upperContourRay_integerComplement n t ht.le

theorem lowerContourWeight_continuousOn (n : ℕ) :
    ContinuousOn (fun t => analyticContourWeight n (lowerContourRay n t)) (Set.Ioi 0) := by
  apply analyticContourWeight_continuousOn n _ (by unfold lowerContourRay; fun_prop)
  · intro t ht
    rw [lowerContourRay_re]
    have : ((67*n:ℕ):ℝ)≤(100*n:ℕ) := by exact_mod_cast (show 67*n≤100*n by omega)
    linarith
  · exact fun t ht => lowerContourRay_integerComplement n t ht

end OddZeta.FourValue

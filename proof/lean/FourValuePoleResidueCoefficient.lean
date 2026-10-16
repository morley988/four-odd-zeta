import FourValuePoleLaurentDecomposition
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section
namespace OddZeta.FourValue
open Polynomial

theorem iteratedPoleSlope_eq_iterate (F : ℂ→ℂ) (a : ℂ) (j : ℕ) :
    iteratedPoleSlope F a j=(Function.swap dslope a)^[j] F := by
  induction j with
  | zero => rfl
  | succ j ih => simpa only [iteratedPoleSlope,Function.iterate_succ_apply',Function.swap] using congrArg (fun f => dslope f a) ih

theorem iteratedPoleSlope_center (F : ℂ→ℂ) (a : ℂ) (hF : AnalyticAt ℂ F a) (j : ℕ) :
    iteratedPoleSlope F a j a=iteratedDeriv j F a/(Nat.factorial j:ℂ) := by
  have hp := hF.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope j
  have hc := hp.coeff_zero 1
  rw [← FormalMultilinearSeries.coeff] at hc
  rw [iteratedPoleSlope_eq_iterate]
  simpa only [FormalMultilinearSeries.coeff_iterate_fslope,zero_add,FormalMultilinearSeries.coeff_ofScalars] using hc.symm

theorem analyticZetaFunction_pole_coefficient (n k : ℕ) (P : ℂ[X]) (hk : 100*n<k) :
    iteratedPoleSlope (analyticZetaFunction n P) (k:ℂ) 4 k=
      iteratedDeriv 4 (analyticZetaFunction n P) (k:ℂ)/24 := by
  have ha : AnalyticAt ℂ (analyticZetaFunction n P) (k:ℂ) :=
    (analyticZetaFunction_poleStrip_differentiableOn n k P (by omega)).analyticAt
      ((poleStrip_isOpen (k:ℤ)).mem_nhds (poleStrip_center_mem (k:ℤ)))
  simpa only [show Nat.factorial 4=24 by rfl,Nat.cast_ofNat] using iteratedPoleSlope_center (analyticZetaFunction n P) (k:ℂ) ha 4
end OddZeta.FourValue

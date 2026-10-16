import FourValueRectangleSums

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory

theorem analyticContour_rectangle_residue (n k : ℕ) (P : ℂ[X]) (hk : 100*n<k) (T : ℝ) (hT : 0<T) :
    poleRectangleBoundary (fun z => analyticZetaFunction n P z*contourKernel z) (k:ℂ) (1/2) T=
      (2*(Real.pi:ℂ)*Complex.I/24)*iteratedDeriv 4 (analyticZetaFunction n P) (k:ℂ) := by
  let F := analyticZetaFunction n P
  let G := contourPoleRegularPart F (k:ℤ)
  let H := contourPolePrincipalTerm F (k:ℤ)
  have hG : DifferentiableOn ℂ G (poleStrip (k:ℤ)) := analyticContourPoleRegularPart_differentiableOn n k P hk
  have hGi : poleRectangleIntegrable G (k:ℂ) (1/2) T := poleRectangleIntegrable_strip G (k:ℤ) T hG.continuousOn
  have hHi : ∀ j : Fin 5,poleRectangleIntegrable (H j) (k:ℂ) (1/2) T :=
    fun j => contourPolePrincipalTerm_integrable F (k:ℤ) j T hT.ne'
  have hSi := poleRectangleIntegrable_sum Finset.univ H (k:ℂ) (1/2) T (fun j _ => hHi j)
  have he : ∀ z : ℂ,z≠(k:ℂ) → F z*contourKernel z=(∑ j : Fin 5,H j z)+G z :=
    fun z hz => contourIntegrand_pole_decomposition_sum F (k:ℤ) z hz
  obtain ⟨h1,h2,h3,h4⟩ := poleRectangle_edges_ne (k:ℂ) (1/2) T (by norm_num) hT.ne'
  have heq := poleRectangleBoundary_congr (fun z => F z*contourKernel z)
    (fun z => (∑ j : Fin 5,H j z)+G z) (k:ℂ) (1/2) T
    (fun x _ => he _ (h1 x)) (fun x _ => he _ (h2 x)) (fun x _ => he _ (h3 x)) (fun x _ => he _ (h4 x))
  have hzero : poleRectangleBoundary G (k:ℂ) (1/2) T=0 := by
    simpa using poleRectangleBoundary_regular_zero G (k:ℤ) T hG
  have hb (j : Fin 5) : poleRectangleBoundary (H j) (k:ℂ) (1/2) T=
      if j=4 then (2*(Real.pi:ℂ)*Complex.I)*iteratedPoleSlope F (k:ℂ) 4 k else 0 := by
    simpa [H] using contourPolePrincipalTerm_boundary F (k:ℤ) j T hT
  change poleRectangleBoundary (fun z => F z*contourKernel z) (k:ℂ) (1/2) T=_
  rw [heq,poleRectangleBoundary_add _ _ _ _ _ hSi hGi,
    poleRectangleBoundary_sum Finset.univ H _ _ _ (fun j _ => hHi j),
    hzero,add_zero]
  simp_rw [hb]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [show F=analyticZetaFunction n P by rfl,analyticZetaFunction_pole_coefficient n k P hk]
  ring
end OddZeta.FourValue

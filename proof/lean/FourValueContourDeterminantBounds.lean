import FourValueContourEnergy

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory

def contourNormalization : ℝ :=
  ‖(1/(2*(Real.pi:ℂ)*Complex.I))‖ * max ‖(3/5-Complex.I : ℂ)‖ ‖(3/5+Complex.I : ℂ)‖

def analyticContourSize (n : ℕ) (P : ℂ[X]) : ℝ :=
  Real.sqrt contourNormalization *
    Real.sqrt (contourRayEnergy n P (lowerContourRay n)+contourRayEnergy n P (upperContourRay n))

theorem contourNormalization_nonneg : 0≤contourNormalization := by
  unfold contourNormalization
  exact mul_nonneg (norm_nonneg _) (le_trans (norm_nonneg _) (le_max_left _ _))

theorem analyticContourSize_nonneg (n : ℕ) (P : ℂ[X]) : 0≤analyticContourSize n P := by
  unfold analyticContourSize
  positivity

theorem analyticContourIntegral_bilinear_bound (n : ℕ) (P Q : ℂ[X])
    (hP : (P*P).natDegree≤361*n+3) (hQ : (Q*Q).natDegree≤361*n+3) :
    ‖analyticContourIntegral n (P*Q)‖≤analyticContourSize n P*analyticContourSize n Q := by
  let l := ∫ t in Set.Ioi (0:ℝ),analyticZetaFunction n (P*Q) (lowerContourRay n t)*contourKernel (lowerContourRay n t)
  let u := ∫ t in Set.Ioi (0:ℝ),analyticZetaFunction n (P*Q) (upperContourRay n t)*contourKernel (upperContourRay n t)
  have hl := contourRay_bilinear_bound n P Q (lowerContourRay n)
    (by unfold lowerContourRay; fun_prop) (lowerContourWeight_continuousOn n)
    (analyticZetaFunction_lowerContour_integrable n _ hP) (analyticZetaFunction_lowerContour_integrable n _ hQ)
  have hu := contourRay_bilinear_bound n P Q (upperContourRay n)
    (by unfold upperContourRay baseContourRay; fun_prop) (upperContourWeight_continuousOn n)
    (analyticZetaFunction_upperContour_integrable n _ hP) (analyticZetaFunction_upperContour_integrable n _ hQ)
  change ‖l‖≤_ at hl
  change ‖u‖≤_ at hu
  have hsum := two_term_sqrt_cauchy_schwarz
    (contourRayEnergy n P (lowerContourRay n)) (contourRayEnergy n Q (lowerContourRay n))
    (contourRayEnergy n P (upperContourRay n)) (contourRayEnergy n Q (upperContourRay n))
    (contourRayEnergy_nonneg _ _ _) (contourRayEnergy_nonneg _ _ _)
    (contourRayEnergy_nonneg _ _ _) (contourRayEnergy_nonneg _ _ _)
  have hval : analyticContourIntegral n (P*Q)=
      (1/(2*(Real.pi:ℂ)*Complex.I))*(l*(3/5-Complex.I)-u*(3/5+Complex.I)) := by
    simp only [analyticContourIntegral,integral_mul_const,l,u]
  have hn : ‖analyticContourIntegral n (P*Q)‖≤contourNormalization*(‖l‖+‖u‖) := by
    rw [hval,norm_mul]
    calc
      _ ≤ ‖(1/(2*(Real.pi:ℂ)*Complex.I))‖ *
          (‖l‖*‖(3/5-Complex.I : ℂ)‖+‖u‖*‖(3/5+Complex.I : ℂ)‖) := by
        gcongr
        simpa only [norm_mul] using norm_sub_le (l*(3/5-Complex.I)) (u*(3/5+Complex.I))
      _ ≤ contourNormalization*(‖l‖+‖u‖) := by
        unfold contourNormalization
        calc
          _ ≤ ‖(1/(2*(Real.pi:ℂ)*Complex.I))‖ *
              (‖l‖*max ‖(3/5-Complex.I : ℂ)‖ ‖(3/5+Complex.I : ℂ)‖+
               ‖u‖*max ‖(3/5-Complex.I : ℂ)‖ ‖(3/5+Complex.I : ℂ)‖) := by
            gcongr
            · exact le_max_left _ _
            · exact le_max_right _ _
          _ = _ := by ring
  calc
    _ ≤ contourNormalization*(‖l‖+‖u‖) := hn
    _ ≤ contourNormalization*(Real.sqrt (contourRayEnergy n P (lowerContourRay n)+contourRayEnergy n P (upperContourRay n))*
        Real.sqrt (contourRayEnergy n Q (lowerContourRay n)+contourRayEnergy n Q (upperContourRay n))) :=
      mul_le_mul_of_nonneg_left ((add_le_add hl hu).trans hsum) contourNormalization_nonneg
    _ = _ := by
      unfold analyticContourSize
      have h := Real.sq_sqrt contourNormalization_nonneg
      conv_lhs => rw [← h]
      ring

def actualAdaptedContourMatrix (n : ℕ) :
    Matrix (Fin (targetHankelDegree n+1)) (Fin (targetHankelDegree n+1)) ℂ :=
  fun i j => analyticContourIntegral n (actualAdaptedBasis n i.val*actualAdaptedBasis n j.val)

theorem actualAdaptedContourMatrix_entry_bound (n : ℕ) (hn : 1≤n)
    (i j : Fin (targetHankelDegree n+1)) :
    ‖actualAdaptedContourMatrix n i j‖≤
      analyticContourSize n (actualAdaptedBasis n i.val)*analyticContourSize n (actualAdaptedBasis n j.val) :=
  analyticContourIntegral_bilinear_bound n _ _
    (actualAdaptedBasis_product_degree n i.val i.val hn (by omega) (by omega))
    (actualAdaptedBasis_product_degree n j.val j.val hn (by omega) (by omega))

theorem actualAdaptedContourMatrix_minor_bound (n : ℕ) (hn : 1≤n) (k : ℕ)
    (rows cols : Fin k→Fin (targetHankelDegree n+1)) :
    ‖((actualAdaptedContourMatrix n).submatrix rows cols).det‖≤(Nat.factorial k:ℝ)*
      (∏ i,analyticContourSize n (actualAdaptedBasis n (rows i).val))*
      (∏ j,analyticContourSize n (actualAdaptedBasis n (cols j).val)) :=
  complex_det_bound _ _ _ (fun _ => analyticContourSize_nonneg _ _)
    (fun _ => analyticContourSize_nonneg _ _) (fun _ _ => actualAdaptedContourMatrix_entry_bound n hn _ _)
end OddZeta.FourValue

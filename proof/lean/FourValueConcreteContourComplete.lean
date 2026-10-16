import FourValueVerticalResidueShift
import FourValueContourDeterminantBounds
import FourValueAnalyticMinorTransfer

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory

/-- The actual sloping contour integral equals the actual odd-zeta linear form. -/
theorem analyticContourIntegral_eq_zeta (n : ℕ) (P : ℂ[X]) (hP : P.natDegree≤361*n+3) :
    analyticContourIntegral n P=analyticZetaFunctional n P := by
  have h := analyticZetaFunctional_eq_vertical n P hP
  have hc : (2*(Real.pi:ℂ)*Complex.I)≠0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  calc
    _ = -(1/(2*(Real.pi:ℂ)*Complex.I))*verticalContourIntegral n P (100*n) :=
      analyticContourIntegral_eq_vertical n P hP
    _ = (1/(2*(Real.pi:ℂ)*Complex.I))*(-verticalContourIntegral n P (100*n)) := by ring
    _ = (1/(2*(Real.pi:ℂ)*Complex.I))*((2*(Real.pi:ℂ)*Complex.I)*analyticZetaFunctional n P) := by rw [h]
    _ = _ := by field_simp

theorem actualAdaptedContourMatrix_eq_zeta (n : ℕ) (hn : 1≤n) :
    actualAdaptedContourMatrix n=actualAdaptedZetaMatrix n := by
  ext i j
  exact analyticContourIntegral_eq_zeta n _
    (actualAdaptedBasis_product_degree n i.val j.val hn (by omega) (by omega))

theorem actualAdaptedZetaMatrix_entry_bound (n : ℕ) (hn : 1≤n)
    (i j : Fin (targetHankelDegree n+1)) :
    ‖actualAdaptedZetaMatrix n i j‖≤
      analyticContourSize n (actualAdaptedBasis n i.val)*analyticContourSize n (actualAdaptedBasis n j.val) := by
  rw [← actualAdaptedContourMatrix_eq_zeta n hn]
  exact actualAdaptedContourMatrix_entry_bound n hn i j

theorem actualAdaptedZetaMatrix_minor_bound (n : ℕ) (hn : 1≤n) (k : ℕ)
    (rows cols : Fin k→Fin (targetHankelDegree n+1)) :
    ‖((actualAdaptedZetaMatrix n).submatrix rows cols).det‖≤(Nat.factorial k:ℝ)*
      (∏ i,analyticContourSize n (actualAdaptedBasis n (rows i).val))*
      (∏ j,analyticContourSize n (actualAdaptedBasis n (cols j).val)) := by
  rw [← actualAdaptedContourMatrix_eq_zeta n hn]
  exact actualAdaptedContourMatrix_minor_bound n hn k rows cols
end OddZeta.FourValue

import FourValueZetaDerivatives

noncomputable section
namespace OddZeta.FourValue
open Polynomial

theorem classicalZetaFunctional_expansion (n : ℕ) (p : ℂ[X]) :
    classicalZetaFunctional n p = physicalTargetFunctional n 8 p +
      15*riemannZeta 7*physicalTargetFunctional n 0 p +
      70*riemannZeta 9*physicalTargetFunctional n 1 p +
      210*riemannZeta 11*physicalTargetFunctional n 2 p +
      495*riemannZeta 13*physicalTargetFunctional n 3 p := by
  rw [classicalZetaFunctional,fourValuePencil_apply]
  simp [classicalZetaPencilCoefficients]

theorem classicalZeta_fourthDeriv_absolutely_summable (n : ℕ) (p : ℂ[X])
    (hp : p.natDegree≤361*n+3) :
    Summable (fun r : ℕ => ‖iteratedDeriv 4 (targetZetaFunction n p) ((r+67*n+1:ℕ):ℂ)/24‖) := by
  exact summable_norm_iff.mpr (classicalZetaFunctional_hasSum_fourthDeriv n p hp).summable

theorem targetZetaFunction_fourthDeriv_gap_zero (n t : ℕ) (ht : 67*n<t)
    (ht' : t≤100*n) (p : ℂ[X]) (hp : p.natDegree≤361*n+3) :
    iteratedDeriv 4 (targetZetaFunction n p) (t:ℂ)=0 := by
  rw [targetZetaFunction_iteratedDeriv n p hp 4 t ht,
    targetZetaTest_gap_zero n t ht ht' p 4 (by decide),mul_zero]

def classicalZetaSeriesMatrix (n : ℕ) :
    Matrix (Fin (targetHankelDegree n+1)) (Fin (targetHankelDegree n+1)) ℂ :=
  fun i j => ∑' r : ℕ, iteratedDeriv 4
    (targetZetaFunction n (squareBasisPolynomial i.val*squareBasisPolynomial j.val))
      ((r+67*n+1:ℕ):ℂ)/24

theorem classicalZetaSeriesMatrix_eq (n : ℕ) :
    classicalZetaSeriesMatrix n = squareBasisGram (classicalZetaFunctional n) (targetHankelDegree n) := by
  ext i j
  exact classicalZetaFunctional_fourthDeriv_tsum n _
    ((target_selected_product_degree n i j).trans (by omega))

/-- Nonzero minors now belong to the actual absolutely convergent derivative
series, with classical riemannZeta values in their exact linear-form identity. -/
theorem classicalZetaSeries_uniform_nonvanishing (n : ℕ) (hn : 1≤n) :
    targetHankelDegree n+1-4≤(classicalZetaSeriesMatrix n).rank ∧
    ∃ rows cols : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1),
      ((classicalZetaSeriesMatrix n).submatrix rows cols).det≠0 := by
  rw [classicalZetaSeriesMatrix_eq]
  exact classicalZeta_uniform_nonvanishing n hn

end OddZeta.FourValue

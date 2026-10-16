import FourValueCorrectedAssembly
import FourValueUniformAnalysisComplete

/-! Exact identification with the analytic zeta matrix and nonzero rational minors.
The physical-coordinate checkpoint remains unchanged; this namespace supplies
the arithmetic statements for the analytic-coordinate matrix. -/

noncomputable section
namespace OddZeta.FourValue.Corrected
open Polynomial

theorem analyticCoordinate_map (P : ℚ[X]) :
    (analyticCoordinate P).map (algebraMap ℚ ℂ) =
      analyticCoordinate (P.map (algebraMap ℚ ℂ)) := by
  simp [analyticCoordinate,Polynomial.map_comp]

theorem fourValuePencil_analytic_ratCast (n : ℕ) (lambda : Fin 4 → ℚ) (P : ℚ[X]) :
    analyticFunctional (fourValuePencil n (fun i => (lambda i:ℂ)))
      (P.map (algebraMap ℚ ℂ)) = (rationalFourValueFunctional n lambda P:ℂ) := by
  change fourValuePencil n (fun i => (lambda i:ℂ))
    (analyticCoordinate (P.map (algebraMap ℚ ℂ))) = _
  rw [← analyticCoordinate_map,fourValuePencil_ratCast]
  rfl

theorem rationalFourValueMatrix_cast (n : ℕ) (lambda : Fin 4 → ℚ) :
    (rationalFourValueMatrix n lambda).map (algebraMap ℚ ℂ) =
      squareBasisGram (analyticFunctional (fourValuePencil n (fun i => (lambda i:ℂ))))
        (targetHankelDegree n) := by
  ext i j
  change (rationalFourValueFunctional n lambda
    (squareBasisPolynomial i.val*squareBasisPolynomial j.val):ℂ) = _
  rw [← fourValuePencil_analytic_ratCast]
  simp [squareBasisGram,Polynomial.map_mul,squareBasisPolynomial_map]

theorem analyticZetaMatrix_rational (n : ℕ) (z : Fin 4 → ℚ)
    (hz : ∀ i : Fin 4, riemannZeta ((![7,9,11,13] : Fin 4 → ℂ) i)=(z i:ℂ)) :
    analyticZetaMatrix n =
      (rationalFourValueMatrix n (fun i => (![15,70,210,495] : Fin 4 → ℚ) i*z i)).map
        (algebraMap ℚ ℂ) := by
  rw [rationalFourValueMatrix_cast]
  have hc : classicalZetaFunctional n =
      fourValuePencil n (fun i => (((![15,70,210,495] : Fin 4 → ℚ) i*z i):ℂ)) := by
    unfold classicalZetaFunctional
    congr 1
    funext i
    fin_cases i <;> simp [classicalZetaPencilCoefficients,← hz]
  unfold analyticZetaMatrix analyticZetaFunctional
  rw [hc]
  simp only [Rat.cast_mul]

theorem analyticZetaMatrix_selected_rational (n : ℕ) (z : Fin 4 → ℚ)
    (hz : ∀ i : Fin 4, riemannZeta ((![7,9,11,13] : Fin 4 → ℂ) i)=(z i:ℂ))
    {k : ℕ} (rows cols : Fin k → Fin (targetHankelDegree n+1)) :
    ((analyticZetaMatrix n).submatrix rows cols).det =
      (((rationalFourValueMatrix n (fun i => (![15,70,210,495] : Fin 4 → ℚ) i*z i)).submatrix rows cols).det:ℂ) := by
  rw [analyticZetaMatrix_rational n z hz]
  change (((rationalFourValueMatrix n (fun i => (![15,70,210,495] : Fin 4 → ℚ) i*z i)).submatrix rows cols).map (algebraMap ℚ ℂ)).det = _
  exact ((algebraMap ℚ ℂ).map_det _).symm

/-- The rational minor is exactly the minor bounded in the analytic checkpoint. -/
theorem analyticZeta_nonzero_minor_allPrime (n : ℕ) (hn : 1≤n) (z : Fin 4 → ℚ)
    (hz : ∀ i : Fin 4,riemannZeta ((![7,9,11,13] : Fin 4 → ℂ) i)=(z i:ℂ)) :
    ∃ (rows cols : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1)) (q : ℚ),
      q≠0 ∧ ((analyticZetaMatrix n).submatrix rows cols).det=(q:ℂ) ∧
      ∀ p : ℕ,∀ hp : p.Prime,
        letI : Fact p.Prime := ⟨hp⟩
        ((targetHankelDegree n+1-4:ℕ):ℤ)*(-40*(Nat.log p (800*n):ℤ)-
          (padicValNat p (rationalPencilDenominator (fun i => (![15,70,210,495] : Fin 4 → ℚ) i*z i)):ℤ))
          ≤padicValRat p q := by
  let lambda : Fin 4 → ℚ := fun i => (![15,70,210,495] : Fin 4 → ℚ) i*z i
  obtain ⟨rows,cols,hne⟩ := analyticZetaMatrix_nonzero_minor n hn
  have he := analyticZetaMatrix_selected_rational n z hz rows cols
  have hq : ((rationalFourValueMatrix n lambda).submatrix rows cols).det≠0 := by
    intro h
    apply hne
    rw [he]
    change (((rationalFourValueMatrix n lambda).submatrix rows cols).det:ℂ)=0
    rw [h]
    simp
  refine ⟨rows,cols,((rationalFourValueMatrix n lambda).submatrix rows cols).det,hq,he,?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  exact (rationalFourValueMatrix_allPrime_minor n lambda rows cols).of_ne_zero hq

/-- In particular, no quadratic-in-n denominator penalty is introduced at 2. -/
theorem corrected_two_adic_minor_bound (n : ℕ) (lambda : Fin 4 → ℚ) {k : ℕ}
    (rows cols : Fin k → Fin (targetHankelDegree n+1)) :
    PadicLower 2 ((k:ℤ)*(-40*(Nat.log 2 (800*n):ℤ)-
      (padicValNat 2 (rationalPencilDenominator lambda):ℤ)))
      ((rationalFourValueMatrix n lambda).submatrix rows cols).det := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact rationalFourValueMatrix_allPrime_minor n lambda rows cols

end OddZeta.FourValue.Corrected

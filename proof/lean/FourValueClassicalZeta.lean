import FourValueZetaBoundary
import FourValueUniformNonvanishing

noncomputable section
namespace OddZeta.FourValue
open Polynomial

def classicalZetaPencilCoefficients : Fin 4 → ℂ :=
  ![15*riemannZeta 7,70*riemannZeta 9,210*riemannZeta 11,495*riemannZeta 13]

def classicalZetaFunctional (n : ℕ) : ℂ[X] →ₗ[ℂ] ℂ :=
  fourValuePencil n classicalZetaPencilCoefficients

theorem targetZetaTest_observation (n : ℕ) (p : ℂ[X]) (i : Fin 9) :
    nineRationalObservations (100*n) i (targetZetaTest n p)=physicalTargetFunctional n i p := rfl

theorem targetZetaTest_zetaForm (n : ℕ) (p : ℂ[X]) (hp : p.natDegree≤361*n+3) :
    rationalZetaForm (100*n) 4 (targetZetaTest n p)=classicalZetaFunctional n p := by
  obtain ⟨c,hc⟩ := targetZetaTest_partialFractions n p hp
  rw [rationalZetaForm_four_values _ _ (targetZetaTest_reflect n p) (targetZetaTest_B1 n p hp) c hc]
  rw [classicalZetaFunctional,fourValuePencil_apply]
  have H := targetZetaTest_observation n p
  have h0 := H 0
  have h1 := H 1
  have h2 := H 2
  have h3 := H 3
  have h8 := H 8
  change rationalB (100*n) 3 (targetZetaTest n p)=physicalTargetFunctional n 0 p at h0
  change rationalB (100*n) 5 (targetZetaTest n p)=physicalTargetFunctional n 1 p at h1
  change rationalB (100*n) 7 (targetZetaTest n p)=physicalTargetFunctional n 2 p at h2
  change rationalB (100*n) 9 (targetZetaTest n p)=physicalTargetFunctional n 3 p at h3
  change rationalC (100*n) 4 (targetZetaTest n p)=physicalTargetFunctional n 8 p at h8
  simpa [classicalZetaPencilCoefficients,h0,h1,h2,h3,h8]

/-- The convergent tail at the original common boundary is exactly the
classical-zeta specialization of the already checked nonvanishing pencil. -/
theorem classicalZetaFunctional_hasSum_common (n : ℕ) (p : ℂ[X])
    (hp : p.natDegree≤361*n+3) :
    HasSum (fun r : ℕ => rationalCoefficientAt ((r+100*n+1:ℕ):ℂ) 4 (targetZetaTest n p))
      (classicalZetaFunctional n p) := by
  obtain ⟨c,hc⟩ := targetZetaTest_partialFractions n p hp
  rw [← targetZetaTest_zetaForm n p hp]
  exact hasSum_rationalZetaForm _ 4 (by decide) _ c hc

/-- Shifting to the manuscript boundary adds only actual order-five zeros. -/
theorem classicalZetaFunctional_hasSum (n : ℕ) (p : ℂ[X])
    (hp : p.natDegree≤361*n+3) :
    HasSum (fun r : ℕ => rationalCoefficientAt ((r+67*n+1:ℕ):ℂ) 4 (targetZetaTest n p))
      (classicalZetaFunctional n p) := by
  let F : ℕ → ℂ := fun r => rationalCoefficientAt ((r+67*n+1:ℕ):ℂ) 4 (targetZetaTest n p)
  have hz : ∑ r ∈ Finset.range (33*n),F r=0 := by
    apply Finset.sum_eq_zero
    intro r hr
    exact targetZetaTest_gap_zero n (r+67*n+1) (by omega) (by
      have := Finset.mem_range.mp hr; omega) p 4 (by decide)
  have hshift : HasSum (fun r => F (r+33*n)) (classicalZetaFunctional n p) := by
    have heq : (fun r => F (r+33*n)) =
        (fun r => rationalCoefficientAt ((r+100*n+1:ℕ):ℂ) 4 (targetZetaTest n p)) := by
      funext r
      dsimp [F]
      rw [show r+33*n+67*n+1=r+100*n+1 by omega]
    rw [heq]
    exact classicalZetaFunctional_hasSum_common n p hp
  have H := (hasSum_nat_add_iff (f:=F) (33*n)).mp hshift
  simpa only [hz,add_zero] using H

theorem classicalZetaFunctional_tsum (n : ℕ) (p : ℂ[X])
    (hp : p.natDegree≤361*n+3) :
    (∑' r : ℕ, rationalCoefficientAt ((r+67*n+1:ℕ):ℂ) 4 (targetZetaTest n p))=
      classicalZetaFunctional n p :=
  (classicalZetaFunctional_hasSum n p hp).tsum_eq

theorem classicalZeta_uniform_nonvanishing (n : ℕ) (hn : 1≤n) :
    let m := targetHankelDegree n
    m+1-4≤(squareBasisGram (classicalZetaFunctional n) m).rank ∧
    ∃ rows cols : Fin (m+1-4) ↪ Fin (m+1),
      ((squareBasisGram (classicalZetaFunctional n) m).submatrix rows cols).det≠0 :=
  fourValue_uniform_nonvanishing n hn classicalZetaPencilCoefficients

end OddZeta.FourValue

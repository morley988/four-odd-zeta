import FourValueCertificatePotential
import FourValueLogBound

noncomputable section
namespace OddZeta.FourValue
open MeasureTheory Set Filter
open scoped Topology

/-- The remaining certificate hypotheses are pointwise bounds and quadrature.
No asymptotic estimate or determinant bound is assumed. -/
theorem analyticZetaMatrix_certificate_asymptotic_bound (V : ℝ→ℝ)
    (hcontinuous : ContinuousOn V (Icc 0 basisLimit)) (L : ℝ)
    (hlower : ∀ s : ℝ,0≤s → s≤basisLimit → L≤V s)
    (hcertificate : ∀ s y : ℝ,0≤s → s≤basisLimit → 0<y →
      certificateG y-2*Real.pi*y+
        s*analyticBasisPotential (concreteBasisWeight s) ((normalizedContourPoint y)^2)≤V s) :
    ∃ E : ℕ→ℝ,
      Tendsto (fun n : ℕ => E n/(n:ℝ)^2) atTop (𝓝 0) ∧
      ∀ n : ℕ,1≤n → ∀ rows cols : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1),
      ‖((analyticZetaMatrix n).submatrix rows cols).det‖≤
        Real.exp ((100*(n:ℝ))^2*contourExponent V+E n) := by
  apply analyticZetaMatrix_uniform_asymptotic_bound V hcontinuous L hlower
  intro s y hs hs1 hy
  rw [contourRate_certificate_expression s y hy]
  exact hcertificate s y hs hs1 hy

theorem analyticZetaMatrix_numerical_rate_of_certificate (V : ℝ→ℝ)
    (hcontinuous : ContinuousOn V (Icc 0 basisLimit)) (L : ℝ)
    (hlower : ∀ s : ℝ,0≤s → s≤basisLimit → L≤V s)
    (hcertificate : ∀ s y : ℝ,0≤s → s≤basisLimit → 0<y →
      certificateG y-2*Real.pi*y+
        s*analyticBasisPotential (concreteBasisWeight s) ((normalizedContourPoint y)^2)≤V s)
    (hquadrature : (∫ s in 0..basisLimit,V s)≤
      (-13277632257660676586509793 / 1024000000000000000000000 : ℝ)) :
    ∃ E : ℕ→ℝ,
      Tendsto (fun n : ℕ => E n/(n:ℝ)^2) atTop (𝓝 0) ∧
      ∀ n : ℕ,1≤n → ∀ rows cols : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1),
      ‖((analyticZetaMatrix n).submatrix rows cols).det‖≤
        Real.exp ((100*(n:ℝ))^2*(-577853339/50000000)+E n) := by
  obtain ⟨E,hE,hbound⟩ := analyticZetaMatrix_certificate_asymptotic_bound V hcontinuous L hlower hcertificate
  refine ⟨E,hE,?_⟩
  intro n hn rows cols
  have hr : contourExponent V≤(-577853339/50000000:ℝ) := by
    have h := LogBound.real_exponent_upper
    unfold contourExponent basisLimit
    norm_num only [show (2:ℝ)*(361/200)=361/100 by norm_num]
    unfold basisLimit at hquadrature
    linarith
  apply (hbound n hn rows cols).trans
  apply Real.exp_le_exp.mpr
  exact add_le_add (mul_le_mul_of_nonneg_left hr (sq_nonneg _)) le_rfl
end OddZeta.FourValue

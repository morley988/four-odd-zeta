import FourValueRiemannError
import FourValueTransferLogError

noncomputable section
namespace OddZeta.FourValue
open MeasureTheory Set Filter
open scoped Topology

def contourRowAverage (f : ℝ→ℝ) (n : ℕ) : ℝ :=
  (1/(100*(n:ℝ)))*∑ j : Fin (targetHankelDegree n+1),f (adaptedIndexMass n j.val)

theorem targetHankel_grid_bounds (n : ℕ) (hn : 1≤n) :
    (targetHankelDegree n:ℝ)/(100*(n:ℝ))≤basisLimit ∧
    basisLimit-(targetHankelDegree n:ℝ)/(100*(n:ℝ))≤1/(100*(n:ℝ)) := by
  have hM : (0:ℝ)<100*(n:ℝ) := by exact_mod_cast (show 0<100*n by omega)
  have hl : 2*targetHankelDegree n≤361*n := by unfold targetHankelDegree; omega
  have hu : 361*n≤2*(targetHankelDegree n+1) := by unfold targetHankelDegree; omega
  have hlR : 2*(targetHankelDegree n:ℝ)≤361*(n:ℝ) := by exact_mod_cast hl
  have huR : 361*(n:ℝ)≤2*((targetHankelDegree n:ℝ)+1) := by exact_mod_cast hu
  constructor
  · apply (div_le_iff₀ hM).mpr
    unfold basisLimit
    nlinarith
  · apply (le_div_iff₀ hM).mpr
    rw [sub_mul,div_mul_cancel₀ _ hM.ne']
    unfold basisLimit
    nlinarith

theorem reciprocal_contour_scale_tendsto_zero :
    Tendsto (fun n : ℕ => 1/(100*(n:ℝ))) atTop (𝓝 0) := by
  simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop (show (0:ℝ)<100 by norm_num))

theorem contourRowAverage_tendsto_integral (f : ℝ→ℝ) (hf : ContinuousOn f (Icc 0 basisLimit)) :
    Tendsto (contourRowAverage f) atTop (𝓝 (∫ s in 0..basisLimit,f s)) := by
  have hC : 0<basisLimit := by norm_num [basisLimit]
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hBabs : ∀ x ∈ Icc 0 basisLimit,|f x|≤B := by simpa only [Real.norm_eq_abs] using hB
  have hB0 : 0≤B := le_trans (abs_nonneg _) (hBabs 0 ⟨le_rfl,hC.le⟩)
  have huc := Metric.uniformContinuousOn_iff.mp (isCompact_Icc.uniformContinuousOn_of_continuous hf)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hmod⟩ := huc (ε/(2*basisLimit)) (by positivity)
  have hsmall : ∀ᶠ n : ℕ in atTop,1/(100*(n:ℝ))<δ :=
    (tendsto_order.mp reciprocal_contour_scale_tendsto_zero).2 δ hδ
  have htail : ∀ᶠ n : ℕ in atTop,2*B*(1/(100*(n:ℝ)))<ε/2 := by
    have h := reciprocal_contour_scale_tendsto_zero.const_mul (2*B)
    simp only [mul_zero] at h
    exact (tendsto_order.mp h).2 (ε/2) (by positivity)
  filter_upwards [eventually_ge_atTop (1:ℕ),hsmall,htail] with n hn hδn htailn
  let M : ℝ := 100*(n:ℝ)
  let N := targetHankelDegree n
  have hM : 0<M := by dsimp [M]; exact_mod_cast (show 0<100*n by omega)
  have hb := targetHankel_grid_bounds n hn
  have hm : ∀ j : ℕ,j<N → ∀ x ∈ Icc ((j:ℝ)/M) (((j:ℝ)+1)/M),|f ((j:ℝ)/M)-f x|≤ε/(2*basisLimit) := by
    intro j hj x hx
    have hjN : (j:ℝ)+1≤N := by exact_mod_cast (show j+1≤N by omega)
    have hjC : ((j:ℝ)+1)/M≤basisLimit := le_trans ((div_le_div_iff_of_pos_right hM).mpr hjN) hb.1
    have hj0 : 0≤(j:ℝ)/M := by positivity
    have hj1 : (j:ℝ)/M≤((j:ℝ)+1)/M := (div_le_div_iff_of_pos_right hM).mpr (by linarith)
    have hdist : dist ((j:ℝ)/M) x<δ := by
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hx.1)]
      have he : ((j:ℝ)+1)/M=(j:ℝ)/M+1/M := by ring
      rw [he] at hx
      change 1/M<δ at hδn
      linarith [hx.2]
    have hh := hmod ((j:ℝ)/M) ⟨hj0,hj1.trans hjC⟩ x ⟨hj0.trans hx.1,hx.2.trans hjC⟩ hdist
    simpa only [Real.dist_eq] using hh.le
  have herror := grid_sum_integral_endpoint_error f basisLimit M B (ε/(2*basisLimit)) hC.le hM N
    hb.1 hb.2 hf hBabs hm (by positivity)
  have heq : contourRowAverage f n=(1/M)*(∑ j∈Finset.range (N+1),f ((j:ℝ)/M)) := by
    unfold contourRowAverage
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => f (adaptedIndexMass n j)) (targetHankelDegree n+1)]
    simp only [adaptedIndexMass,Nat.cast_mul,Nat.cast_ofNat]
    rfl
  rw [Real.dist_eq,heq]
  have hmain : basisLimit*(ε/(2*basisLimit))=ε/2 := by field_simp
  rw [hmain] at herror
  change 2*B*(1/M)<ε/2 at htailn
  have htailn' : 2*B/M<ε/2 := by simpa only [div_eq_mul_inv,one_mul] using htailn
  linarith
end OddZeta.FourValue

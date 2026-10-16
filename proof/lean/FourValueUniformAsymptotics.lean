import FourValueMinorOverhead
import FourValueRowRateIntegral

noncomputable section
namespace OddZeta.FourValue
open MeasureTheory Set Filter
open scoped Topology

def contourExponent (V : ℝ→ℝ) : ℝ :=
  (∫ s in 0..basisLimit,V s)-2*basisLimit^2*Real.log (2*basisLimit)+3*basisLimit^2

def uniformAnalyticError (V : ℝ→ℝ) (L D : ℝ) (n : ℕ) : ℝ :=
  (100*(n:ℝ))^2*(contourRowAverage (contourRowRate V) n-contourExponent V)+minorLogOverhead n L D

theorem uniformAnalyticError_normalized_tendsto_zero (V : ℝ→ℝ)
    (hV : ContinuousOn V (Icc 0 basisLimit)) (L D : ℝ) :
    Tendsto (fun n : ℕ => uniformAnalyticError V L D n/(n:ℝ)^2) atTop (𝓝 0) := by
  have hrow := contourRowAverage_tendsto_integral (contourRowRate V) (contourRowRate_continuousOn V hV)
  rw [contourRowRate_integral V hV] at hrow
  change Tendsto _ _ (𝓝 (contourExponent V)) at hrow
  have hr := (hrow.sub_const (contourExponent V)).const_mul (10000:ℝ)
  simp only [sub_self,mul_zero] at hr
  have h := hr.add (minorLogOverhead_normalized_tendsto_zero L D)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  unfold uniformAnalyticError
  field_simp
  <;> ring

theorem analyticZetaMatrix_uniform_asymptotic_bound (V : ℝ→ℝ)
    (hcontinuous : ContinuousOn V (Icc 0 basisLimit)) (L : ℝ)
    (hlower : ∀ s : ℝ,0≤s → s≤basisLimit → L≤V s)
    (hcertificate : ∀ s y : ℝ,0≤s → s≤basisLimit → 0<y → contourRate s y≤V s) :
    ∃ E : ℕ→ℝ,
      Tendsto (fun n : ℕ => E n/(n:ℝ)^2) atTop (𝓝 0) ∧
      ∀ n : ℕ,1≤n → ∀ rows cols : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1),
      ‖((analyticZetaMatrix n).submatrix rows cols).det‖≤
        Real.exp ((100*(n:ℝ))^2*contourExponent V+E n) := by
  obtain ⟨D,hD,hminor⟩ := actualAdaptedZetaMatrix_uniform_minor_bound L
  refine ⟨uniformAnalyticError V L D,uniformAnalyticError_normalized_tendsto_zero V hcontinuous L D,?_⟩
  intro n hn rows cols
  let M : ℝ := 100*(n:ℝ)
  let k := analyticMinorSize n
  let S := ∑ j : Fin (targetHankelDegree n+1),contourRowRate V (adaptedIndexMass n j.val)
  let A := M*S-4*M*(L-24)+(k:ℝ)*(Real.log M+Real.log D)
  let H := (Nat.factorial k:ℝ)*Real.exp A
  have hH : 0≤H := by dsimp [H]; positivity
  have hall (r c : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1)) :
      ‖((actualAdaptedZetaMatrix n).submatrix r c).det‖≤H := hminor n hn V hlower hcertificate r c
  have ht := analyticZetaMatrix_minor_transfer n hn H hH hall rows cols
  have hM : 0<M := by dsimp [M]; exact_mod_cast (show 0<100*n by omega)
  have hf : 0<(Nat.factorial k:ℝ) := by positivity
  have hT : 0<actualAnalyticTransferFactor n := lt_of_lt_of_le (by norm_num) (actualAnalyticTransferFactor_ge_one n hn)
  have hrow : M^2*contourRowAverage (contourRowRate V) n=M*S := by
    unfold contourRowAverage
    change M^2*((1/M)*S)=M*S
    field_simp
  have hexp : H*(actualAnalyticTransferFactor n)^2=
      Real.exp (M^2*contourExponent V+uniformAnalyticError V L D n) := by
    dsimp [H]
    rw [← Real.exp_log hf,← Real.exp_log hT]
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    unfold uniformAnalyticError minorLogOverhead
    change Real.log (Nat.factorial k:ℝ)+A+2*Real.log (actualAnalyticTransferFactor n)=
      M^2*contourExponent V+(M^2*(contourRowAverage (contourRowRate V) n-contourExponent V)+
      (Real.log (Nat.factorial k:ℝ)+(k:ℝ)*(Real.log M+Real.log D)-4*M*(L-24)+2*Real.log (actualAnalyticTransferFactor n)))
    dsimp [A]
    nlinarith only [hrow]
  exact ht.trans_eq hexp
end OddZeta.FourValue

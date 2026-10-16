import FourValueContourResidues

noncomputable section
namespace OddZeta.FourValue
open Polynomial Filter MeasureTheory
open scoped Topology

def verticalContourLine (a : ℤ) (t : ℝ) : ℂ := (a:ℂ)+1/2+Complex.I*(t:ℂ)

theorem verticalContourLine_integerComplement (a : ℤ) (t : ℝ) :
    verticalContourLine a t∈Complex.integerComplement := by
  rintro ⟨k,hk⟩
  have hi := congrArg Complex.im hk
  simp [verticalContourLine] at hi
  have hr := congrArg Complex.re hk
  simp [verticalContourLine] at hr
  have hr' : (2:ℝ)*((k:ℝ)-(a:ℝ))=1 := by linarith
  have hrZ : (2:ℤ)*(k-a)=1 := by exact_mod_cast hr'
  omega

theorem contourKernel_vertical_bound : ∃ C : ℝ,0≤C ∧ ∀ a : ℤ,∀ t : ℝ,
    ‖contourKernel (verticalContourLine a t)‖≤C*Real.exp (-2*Real.pi*|t|) := by
  obtain ⟨C,hC,h⟩ := contourKernel_baseRay_bound 0
  refine ⟨C,hC,fun a t => ?_⟩
  by_cases ht : 0≤t
  · have he : verticalContourLine a t=baseContourRay 0 t+(a:ℂ) := by
      simp [verticalContourLine,baseContourRay]; ring
    rw [he,contourKernel_int_period,abs_of_nonneg ht]
    exact h t ht
  · have he : -verticalContourLine a t=baseContourRay 0 (-t)+((-a-1:ℤ):ℂ) := by
      simp [verticalContourLine,baseContourRay]; ring
    rw [← norm_neg (contourKernel _),← contourKernel_neg,he,contourKernel_int_period,
      abs_of_neg (lt_of_not_ge ht)]
    exact h (-t) (by linarith)

def partialFractionCoefficientBound (b : ℕ) (c : ℤ→Fin 10→ℂ) : ℝ :=
  ∑ j∈poleWindow b,∑ k : Fin 10,‖c j k‖

theorem partialFractionCoefficientBound_nonneg (b : ℕ) (c : ℤ→Fin 10→ℂ) :
    0≤partialFractionCoefficientBound b c := by unfold partialFractionCoefficientBound; positivity

theorem partialFractionValue_decay (b : ℕ) (c : ℤ→Fin 10→ℂ) (δ : ℝ) (hδ : 1≤δ)
    (z : ℂ) (hz : (b:ℝ)+δ≤z.re) :
    ‖partialFractionValue b c 0 z‖≤partialFractionCoefficientBound b c/δ := by
  have hδ0 : 0<δ := by linarith
  unfold partialFractionValue partialFractionCoefficientBound
  rw [Finset.sum_div]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.sum_div]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  have hjr : (j:ℝ)≤b := by exact_mod_cast (Finset.mem_Icc.mp hj).2
  have hn := Complex.re_le_norm (z-(j:ℂ))
  simp only [Complex.sub_re,Complex.intCast_re] at hn
  have hb : δ≤‖z-(j:ℂ)‖ := by linarith
  have hn1 : 1≤‖z-(j:ℂ)‖ := hδ.trans hb
  have hp : δ≤‖z-(j:ℂ)‖^(k.val+1) := hb.trans (le_self_pow₀ hn1 (by omega))
  have hi := one_div_le_one_div_of_le hδ0 hp
  simp only [norm_mul,poleTaylorValue,pow_zero,Nat.add_zero,Nat.choose_zero_right,
    Nat.cast_one,one_mul,norm_div,norm_one,norm_pow]
  simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hi (norm_nonneg (c j k))

theorem analyticZetaFunction_right_decay (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) : ∃ B : ℝ,0≤B ∧ ∀ δ : ℝ,1≤δ → ∀ z : ℂ,
      ((100*n:ℕ):ℝ)+δ≤z.re → ‖analyticZetaFunction n P z‖≤B/δ := by
  obtain ⟨c,hc⟩ := analyticZetaFunction_partialFractions n P hP
  refine ⟨partialFractionCoefficientBound (100*n) c,partialFractionCoefficientBound_nonneg _ _,fun δ hδ z hz => ?_⟩
  rw [hc z (by linarith)]
  exact partialFractionValue_decay _ _ δ hδ z hz

theorem analyticZetaFunction_vertical_decay (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) : ∃ B : ℝ,0≤B ∧ ∀ N : ℕ,∀ t : ℝ,
    ‖analyticZetaFunction n P (verticalContourLine (100*n+N+1:ℕ) t)*
      contourKernel (verticalContourLine (100*n+N+1:ℕ) t)‖≤
      (B/((N:ℝ)+1))*Real.exp (-2*Real.pi*|t|) := by
  obtain ⟨B,hB,hb⟩ := analyticZetaFunction_right_decay n P hP
  obtain ⟨C,hC,hc⟩ := contourKernel_vertical_bound
  refine ⟨B*C,mul_nonneg hB hC,fun N t => ?_⟩
  have hδ : (1:ℝ)≤(N:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) N]
  have hr := hb ((N:ℝ)+1) hδ (verticalContourLine (100*n+N+1:ℕ) t) (by
    simp [verticalContourLine]; push_cast; linarith)
  rw [norm_mul]
  calc
    _ ≤ (B/((N:ℝ)+1))*(C*Real.exp (-2*Real.pi*|t|)) :=
      mul_le_mul hr (hc _ t) (norm_nonneg _) (div_nonneg hB (by positivity))
    _ = _ := by ring
end OddZeta.FourValue

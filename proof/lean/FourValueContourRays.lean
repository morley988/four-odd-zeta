import FourValueContourKernel
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
namespace OddZeta.FourValue

def baseContourRay (κ t : ℝ) : ℂ := (1/2:ℂ)+((κ:ℂ)+Complex.I)*(t:ℂ)
def upperContourRay (n : ℕ) (t : ℝ) : ℂ := baseContourRay (3/5) t+(100*n:ℕ)

theorem baseContourRay_im (κ t : ℝ) : (baseContourRay κ t).im=t := by
  simp [baseContourRay]

theorem baseContourRay_integerComplement (κ t : ℝ) (ht : 0≤t) :
    baseContourRay κ t∈Complex.integerComplement := by
  rintro ⟨k,hk⟩
  have hi := congrArg Complex.im hk
  simp [baseContourRay] at hi
  have hr := congrArg Complex.re hk
  simp [baseContourRay,← hi] at hr
  have hr' : (2:ℝ)*(k:ℝ)=1 := by linarith
  have hk' : (2:ℤ)*k=1 := by exact_mod_cast hr'
  omega

theorem contourKernel_continuousOn : ContinuousOn contourKernel Complex.integerComplement := by
  have hd : ContDiffOn ℂ 4 (fun z : ℂ => (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*z))
      Complex.integerComplement := by
    unfold Complex.cot
    apply ContDiffOn.mul contDiffOn_const
    exact ContDiffOn.div (by fun_prop) (by fun_prop) (fun z hz => sin_pi_mul_ne_zero hz)
  have hc := hd.continuousOn_iteratedDerivWithin (m:=4) le_rfl
    Complex.isOpen_compl_range_intCast.uniqueDiffOn
  have hc' : ContinuousOn (iteratedDeriv 4
      (fun z : ℂ => (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*z))) Complex.integerComplement := by
    apply hc.congr
    intro z hz
    exact (iteratedDerivWithin_of_isOpen Complex.isOpen_compl_range_intCast hz).symm
  exact hc'.div_const 24

theorem contourKernel_int_period (k : ℤ) (z : ℂ) : contourKernel (z+k)=contourKernel z := by
  have hf : (fun z : ℂ => (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*(z+k))) =
      (fun z : ℂ => (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*z)) := by
    funext z
    rw [Complex.cot_pi_eq_exp_ratio,Complex.cot_pi_eq_exp_ratio]
    have he : Complex.exp (2*(Real.pi:ℂ)*Complex.I*(z+k))=
        Complex.exp (2*(Real.pi:ℂ)*Complex.I*z) := by
      rw [mul_add,Complex.exp_add]
      have he' : Complex.exp (2*(Real.pi:ℂ)*Complex.I*(k:ℂ))=1 := by
        simpa [mul_comm] using Complex.exp_int_mul_two_pi_mul_I k
      rw [he',mul_one]
    rw [he]
  have hshift := congrFun (iteratedDeriv_comp_add_const (n:=4)
    (f:=fun z : ℂ => (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*z)) (s:=(k:ℂ))) z
  unfold contourKernel
  rw [← hshift,hf]

theorem contourKernel_baseRay_bound (κ : ℝ) : ∃ C : ℝ, 0≤C ∧ ∀ t : ℝ, 0≤t →
    ‖contourKernel (baseContourRay κ t)‖≤C*Real.exp (-2*Real.pi*t) := by
  have hc : ContinuousOn (fun t : ℝ => contourKernel (baseContourRay κ t)*
      (Real.exp (2*Real.pi*t):ℂ)) (Set.Icc 0 1) := by
    apply ContinuousOn.mul
    · apply contourKernel_continuousOn.comp (by unfold baseContourRay; fun_prop)
      intro t ht
      exact baseContourRay_integerComplement κ t ht.1
    · fun_prop
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let A := (2*Real.pi)^5/24*fourthPowerMajorant (Real.exp (-2*Real.pi))
  refine ⟨max 0 (max B A),le_max_left _ _,fun t ht => ?_⟩
  by_cases ht1 : t≤1
  · have hb := hB t ⟨ht,ht1⟩
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at hb
    have he : Real.exp (2*Real.pi*t)*Real.exp (-2*Real.pi*t)=1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    calc
      _ = (‖contourKernel (baseContourRay κ t)‖*Real.exp (2*Real.pi*t))*Real.exp (-2*Real.pi*t) := by rw [mul_assoc,he,mul_one]
      _ ≤ B*Real.exp (-2*Real.pi*t) := mul_le_mul_of_nonneg_right hb (le_of_lt (Real.exp_pos _))
      _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_left B A).trans (le_max_right _ _)) (le_of_lt (Real.exp_pos _))
  · have hb := contourKernel_upper_bound (baseContourRay κ t) (by rw [baseContourRay_im]; linarith)
    rw [baseContourRay_im] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right ((le_max_right B A).trans (le_max_right _ _)) (le_of_lt (Real.exp_pos _)))

theorem contourKernel_upperRay_bound : ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, ∀ t : ℝ, 0≤t →
    ‖contourKernel (upperContourRay n t)‖≤C*Real.exp (-2*Real.pi*t) := by
  obtain ⟨C,hC,h⟩ := contourKernel_baseRay_bound (3/5)
  refine ⟨C,hC,fun n t ht => ?_⟩
  have hp := contourKernel_int_period (100*n:ℕ) (baseContourRay (3/5) t)
  unfold upperContourRay
  rw [show contourKernel (baseContourRay (3/5) t+(100*n:ℕ))=contourKernel (baseContourRay (3/5) t) by exact_mod_cast hp]
  exact h t ht

theorem contourKernel_neg (z : ℂ) : contourKernel (-z)= -contourKernel z := by
  let f : ℂ→ℂ := fun z => (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*z)
  have hf : (fun z => f (-z)) = (fun z => -f z) := by
    funext z
    simp [f,Complex.cot,Complex.cos_neg,Complex.sin_neg,div_neg,mul_neg]
  have hd := iteratedDeriv_comp_neg 4 f z
  rw [hf,iteratedDeriv_fun_neg] at hd
  norm_num at hd
  change iteratedDeriv 4 f (-z)/24= -(iteratedDeriv 4 f z/24)
  rw [← hd,neg_div]

def lowerContourRay (n : ℕ) (t : ℝ) : ℂ :=
  (100*n:ℕ)+(1/2:ℂ)+(3/5-Complex.I)*(t:ℂ)

theorem lowerContourRay_reflection (n : ℕ) (t : ℝ) :
    -lowerContourRay n t=baseContourRay (-3/5) t-((100*n+1:ℕ):ℂ) := by
  unfold lowerContourRay baseContourRay
  push_cast
  ring

theorem contourKernel_lowerRay_bound : ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, ∀ t : ℝ, 0≤t →
    ‖contourKernel (lowerContourRay n t)‖≤C*Real.exp (-2*Real.pi*t) := by
  obtain ⟨C,hC,h⟩ := contourKernel_baseRay_bound (-3/5)
  refine ⟨C,hC,fun n t ht => ?_⟩
  have hp := contourKernel_int_period (-((100*n+1:ℕ):ℤ)) (baseContourRay (-3/5) t)
  have hr : ‖contourKernel (lowerContourRay n t)‖=‖contourKernel (baseContourRay (-3/5) t)‖ := by
    rw [← norm_neg (contourKernel _),← contourKernel_neg,lowerContourRay_reflection]
    have he : contourKernel (baseContourRay (-3/5) t-((100*n+1:ℕ):ℂ))=
        contourKernel (baseContourRay (-3/5) t) := by simpa only [Int.cast_neg,Int.cast_natCast,sub_eq_add_neg] using hp
    rw [he]
  rw [hr]
  exact h t ht

theorem contourKernel_bothRays_bound : ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, ∀ t : ℝ, 0≤t →
    ‖contourKernel (upperContourRay n t)‖≤C*Real.exp (-2*Real.pi*t) ∧
    ‖contourKernel (lowerContourRay n t)‖≤C*Real.exp (-2*Real.pi*t) := by
  obtain ⟨U,hU,hu⟩ := contourKernel_upperRay_bound
  obtain ⟨L,hL,hl⟩ := contourKernel_lowerRay_bound
  refine ⟨max U L,hU.trans (le_max_left _ _),fun n t ht => ⟨?_,?_⟩⟩
  · exact (hu n t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt (Real.exp_pos _)))
  · exact (hl n t ht).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt (Real.exp_pos _)))
end OddZeta.FourValue

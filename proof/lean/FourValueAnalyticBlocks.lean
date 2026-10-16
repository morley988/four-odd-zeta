import FourValueAnalyticCoordinates
import FourValueGeometry

noncomputable section
namespace OddZeta.FourValue
open Polynomial

/-- A zero-sized block contributes one, not the zero polynomial. -/
def analyticBlock (c : ℂ) (δ : ℝ) (m : ℕ) : ℂ[X] :=
  if m=0 then 1 else (X-C c)^m-C ((δ:ℂ)^m)

theorem analyticBlock_zero (c : ℂ) (δ : ℝ) : analyticBlock c δ 0=1 := by
  simp [analyticBlock]

theorem analyticBlock_monic (c : ℂ) (δ : ℝ) (m : ℕ) :
    (analyticBlock c δ m).Monic := by
  by_cases hm : m=0
  · simp [analyticBlock,hm]
  · rw [analyticBlock,if_neg hm]
    apply ((monic_X_sub_C c).pow m).sub_of_left
    apply lt_of_le_of_lt (degree_C_le)
    simpa using (show (0 : WithBot ℕ)<m from WithBot.coe_lt_coe.mpr (Nat.pos_of_ne_zero hm))

theorem analyticBlock_natDegree (c : ℂ) (δ : ℝ) (m : ℕ) :
    (analyticBlock c δ m).natDegree=m := by
  by_cases hm : m=0
  · simp [analyticBlock,hm]
  · rw [analyticBlock,if_neg hm,natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simp [Nat.pos_of_ne_zero hm]

theorem analyticBlock_eval_bound (c z : ℂ) (δ : ℝ) (hδ : 0≤δ) (m : ℕ) :
    ‖(analyticBlock c δ m).eval z‖≤2*(max ‖z-c‖ δ)^m := by
  by_cases hm : m=0
  · simp [analyticBlock,hm]
  · simpa [analyticBlock,hm,abs_of_nonneg hδ] using
      Geometry.power_difference_bound (z-c) (δ:ℂ) m

theorem analyticBlock_root_bound (c z : ℂ) (δ R : ℝ) (hδ : 0≤δ) (m : ℕ)
    (hc : ‖c‖+δ≤R) (hz : (analyticBlock c δ m).eval z=0) : ‖z‖≤R := by
  by_cases hm : m=0
  · simp [analyticBlock,hm] at hz
  · apply Geometry.block_root_bound z c δ R hδ m hm _ hc
    simpa [analyticBlock,hm] using hz

/-- Paired blocks ensure a real polynomial when the centers are conjugate. -/
def analyticBlockPair (c : ℂ) (δ : ℝ) (m : ℕ) : ℂ[X] :=
  analyticBlock c δ m * analyticBlock (star c) δ m

theorem analyticBlockPair_monic (c : ℂ) (δ : ℝ) (m : ℕ) :
    (analyticBlockPair c δ m).Monic :=
  (analyticBlock_monic c δ m).mul (analyticBlock_monic (star c) δ m)

theorem analyticBlockPair_natDegree (c : ℂ) (δ : ℝ) (m : ℕ) :
    (analyticBlockPair c δ m).natDegree=2*m := by
  rw [analyticBlockPair,natDegree_mul (analyticBlock_monic c δ m).ne_zero
    (analyticBlock_monic (star c) δ m).ne_zero,analyticBlock_natDegree,analyticBlock_natDegree]
  omega

theorem analyticBlockPair_eval_bound (c z : ℂ) (δ : ℝ) (hδ : 0≤δ) (m : ℕ) :
    ‖(analyticBlockPair c δ m).eval z‖ ≤
      4*((max ‖z-c‖ δ)*(max ‖z-star c‖ δ))^m := by
  rw [analyticBlockPair,eval_mul,norm_mul]
  calc
    _ ≤ (2*(max ‖z-c‖ δ)^m)*(2*(max ‖z-star c‖ δ)^m) :=
      mul_le_mul (analyticBlock_eval_bound c z δ hδ m)
        (analyticBlock_eval_bound (star c) z δ hδ m) (norm_nonneg _) (by positivity)
    _ = _ := by rw [mul_pow]; ring

theorem analyticBlockPair_root_bound (c z : ℂ) (δ R : ℝ) (hδ : 0≤δ) (m : ℕ)
    (hc : ‖c‖+δ≤R) (hz : (analyticBlockPair c δ m).eval z=0) : ‖z‖≤R := by
  simp only [analyticBlockPair,eval_mul,mul_eq_zero] at hz
  rcases hz with hz|hz
  · exact analyticBlock_root_bound c z δ R hδ m hc hz
  · exact analyticBlock_root_bound (star c) z δ R hδ m (by simpa using hc) hz

variable {ι : Type*} [Fintype ι]

def analyticBasisPolynomial (centers : ι→ℂ) (δ : ℝ) (m : ι→ℕ) (d : ℕ) : ℂ[X] :=
  (X-C 1)^d * ∏ l, analyticBlockPair (centers l) δ (m l)

theorem analyticBasisPolynomial_monic (centers : ι→ℂ) (δ : ℝ) (m : ι→ℕ) (d : ℕ) :
    (analyticBasisPolynomial centers δ m d).Monic := by
  apply ((monic_X_sub_C 1).pow d).mul
  exact monic_prod_of_monic _ _ (fun l _ => analyticBlockPair_monic _ _ _)

theorem analyticBasisPolynomial_natDegree (centers : ι→ℂ) (δ : ℝ) (m : ι→ℕ) (d : ℕ) :
    (analyticBasisPolynomial centers δ m d).natDegree=d+∑ l,2*m l := by
  rw [analyticBasisPolynomial,natDegree_mul ((monic_X_sub_C 1).pow d).ne_zero
    (monic_prod_of_monic _ _ (fun l _ => analyticBlockPair_monic (centers l) δ (m l))).ne_zero]
  rw [natDegree_pow, natDegree_X_sub_C]
  rw [natDegree_prod_of_monic _ _ (fun l _ => analyticBlockPair_monic (centers l) δ (m l))]
  simp only [mul_one, analyticBlockPair_natDegree]

theorem analyticBasisPolynomial_root_bound (centers : ι→ℂ) (δ R : ℝ) (m : ι→ℕ)
    (d : ℕ) (hδ : 0≤δ) (hR : 1≤R) (hc : ∀ l, ‖centers l‖+δ≤R)
    (z : ℂ) (hz : (analyticBasisPolynomial centers δ m d).eval z=0) : ‖z‖≤R := by
  classical
  simp only [analyticBasisPolynomial,eval_mul,eval_pow,eval_sub,eval_X,eval_C,
    eval_prod,mul_eq_zero] at hz
  rcases hz with hz|hz
  · have h := eq_zero_of_pow_eq_zero hz
    have : z=1 := sub_eq_zero.mp h
    simpa [this] using hR
  · obtain ⟨l,_,hl⟩ := Finset.prod_eq_zero_iff.mp hz
    exact analyticBlockPair_root_bound _ z δ R hδ _ (hc l) hl

theorem analyticBasisPolynomial_eval_bound (centers : ι→ℂ) (δ : ℝ) (m : ι→ℕ)
    (d : ℕ) (hδ : 0≤δ) (z : ℂ) :
    ‖(analyticBasisPolynomial centers δ m d).eval z‖ ≤
      ‖z-1‖^d * 4^(Fintype.card ι) *
        ∏ l, ((max ‖z-centers l‖ δ)*(max ‖z-star (centers l)‖ δ))^(m l) := by
  classical
  simp only [analyticBasisPolynomial,eval_mul,eval_pow,eval_sub,eval_X,eval_C,
    eval_prod,norm_mul,norm_pow,norm_prod]
  calc
    _ ≤ ‖z-1‖^d * ∏ l, (4*((max ‖z-centers l‖ δ)*(max ‖z-star (centers l)‖ δ))^(m l)) := by
      gcongr with l
      exact analyticBlockPair_eval_bound _ _ _ hδ _
    _ = _ := by rw [Finset.prod_mul_distrib]; simp [mul_assoc]
end OddZeta.FourValue

import FourValueAnalyticBlocks

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {ι : Type*} [Fintype ι]

def roundedBlockSize (i : ℕ) (w : ι→ℝ) (l : ι) : ℕ := ⌊(i:ℝ)*w l/2⌋₊
def roundedRemainder (i : ℕ) (w : ι→ℝ) : ℕ := i-∑ l,2*roundedBlockSize i w l

theorem roundedBlockSize_sum_le (i : ℕ) (w : ι→ℝ) (hw : ∀ l, 0≤w l)
    (hs : ∑ l,w l=1) : (∑ l,2*roundedBlockSize i w l) ≤ i := by
  have h : ∀ l, (2*roundedBlockSize i w l:ℝ) ≤ (i:ℝ)*w l := by
    intro l
    have hw0 := hw l
    have := Nat.floor_le (show 0≤(i:ℝ)*w l/2 by positivity)
    dsimp [roundedBlockSize]
    linarith
  have hsum := Finset.sum_le_sum (fun l (_ : l∈Finset.univ) => h l)
  simp only [← Finset.mul_sum,hs,mul_one] at hsum
  rw [Finset.mul_sum] at hsum
  exact_mod_cast hsum

theorem roundedRemainder_degree (i : ℕ) (w : ι→ℝ) (hw : ∀ l, 0≤w l)
    (hs : ∑ l,w l=1) : roundedRemainder i w+∑ l,2*roundedBlockSize i w l=i :=
  Nat.sub_add_cancel (roundedBlockSize_sum_le i w hw hs)

theorem roundedRemainder_lt (i : ℕ) (w : ι→ℝ) (hw : ∀ l, 0≤w l)
    (hs : ∑ l,w l=1) : roundedRemainder i w<2*Fintype.card ι := by
  have hne : Nonempty ι := by
    by_contra h
    haveI : IsEmpty ι := not_nonempty_iff.mp h
    simp at hs
  have hsum : (∑ l, (i:ℝ)*w l) < ∑ l, (2*(roundedBlockSize i w l:ℝ)+2) := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro l _
    have := Nat.lt_floor_add_one ((i:ℝ)*w l/2)
    dsimp [roundedBlockSize]
    linarith
  rw [← Finset.mul_sum,hs,mul_one,Finset.sum_add_distrib] at hsum
  have hd := roundedRemainder_degree i w hw hs
  have hdc : (roundedRemainder i w:ℝ)+∑ l,2*(roundedBlockSize i w l:ℝ)=(i:ℝ) := by exact_mod_cast hd
  have hb : (roundedRemainder i w:ℝ)<2*(Fintype.card ι:ℝ) := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
    linarith
  exact_mod_cast hb

def roundedAnalyticBasis (centers : ι→ℂ) (δ : ℝ) (i : ℕ) (w : ι→ℝ) : ℂ[X] :=
  analyticBasisPolynomial centers δ (roundedBlockSize i w) (roundedRemainder i w)

theorem roundedAnalyticBasis_monic (centers : ι→ℂ) (δ : ℝ) (i : ℕ) (w : ι→ℝ) :
    (roundedAnalyticBasis centers δ i w).Monic := analyticBasisPolynomial_monic _ _ _ _

theorem roundedAnalyticBasis_natDegree (centers : ι→ℂ) (δ : ℝ) (i : ℕ) (w : ι→ℝ)
    (hw : ∀ l,0≤w l) (hs : ∑ l,w l=1) :
    (roundedAnalyticBasis centers δ i w).natDegree=i := by
  rw [roundedAnalyticBasis,analyticBasisPolynomial_natDegree,roundedRemainder_degree i w hw hs]

theorem roundedAnalyticBasis_root_bound (centers : ι→ℂ) (δ R : ℝ) (i : ℕ)
    (w : ι→ℝ) (hδ : 0≤δ) (hR : 1≤R) (hc : ∀ l, ‖centers l‖+δ≤R)
    (z : ℂ) (hz : (roundedAnalyticBasis centers δ i w).eval z=0) : ‖z‖≤R :=
  analyticBasisPolynomial_root_bound centers δ R _ _ hδ hR hc z hz
end OddZeta.FourValue

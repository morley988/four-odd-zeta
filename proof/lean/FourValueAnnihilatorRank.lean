import FourValueSelectedBasisValuations

noncomputable section
namespace OddZeta.FourValue
open Polynomial

theorem polynomialGram_rank_le_annihilator {k : ℕ} (L : ℚ[X] →ₗ[ℚ] ℚ)
    (P Q : Fin k → ℚ[X]) (R : ℚ[X]) (hR : R.Monic) (hann : ∀ f,L (R*f)=0) :
    (polynomialGram L P Q).rank≤R.natDegree := by
  by_cases hR1 : R=1
  · have hL (f : ℚ[X]) : L f=0 := by simpa [hR1] using hann f
    have he : polynomialGram L P Q=0 := by ext i j; exact hL _
    simp [he]
  let U : Matrix (Fin k) (Fin R.natDegree) ℚ := fun i l => (P i %ₘ R).coeff l.val
  let V : Matrix (Fin R.natDegree) (Fin k) ℚ := fun l j => L (X^l.val*Q j)
  have he : polynomialGram L P Q=U*V := by
    ext i j
    have hmod : L ((P i %ₘ R)*Q j)=L (P i*Q j) := by
      have h := congrArg (fun f => L (f*Q j)) (Polynomial.modByMonic_add_div (P i) R)
      simpa only [add_mul,mul_assoc,map_add,hann,add_zero] using h
    change L (P i*Q j)=_
    rw [← hmod,(P i %ₘ R).as_sum_range_C_mul_X_pow' (Polynomial.natDegree_modByMonic_lt _ hR hR1)]
    simp only [Finset.sum_mul,map_sum,← Fin.sum_univ_eq_sum_range,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro l hl
    change L (C ((P i %ₘ R).coeff l.val)*X^l.val*Q j)=_
    rw [mul_assoc,← smul_eq_C_mul,map_smul]
    rfl
  rw [he]
  exact (Matrix.rank_mul_le_left U V).trans (by simpa using Matrix.rank_le_card_width U)

theorem polynomialGram_det_zero_of_capacity {k : ℕ} (L : ℚ[X] →ₗ[ℚ] ℚ)
    (P Q : Fin k → ℚ[X]) (R : ℚ[X]) (hR : R.Monic) (hann : ∀ f,L (R*f)=0)
    (hk : R.natDegree<k) : (polynomialGram L P Q).det=0 := by
  by_contra hd
  have hr := polynomialGram_rank_le_annihilator L P Q R hR hann
  rw [Matrix.rank_of_det_ne_zero hd,Fintype.card_fin] at hr
  omega
end OddZeta.FourValue

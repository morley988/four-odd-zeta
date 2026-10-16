import FourValueConcreteBasis

noncomputable section
set_option maxHeartbeats 200000
namespace OddZeta.FourValue

/-- The product of the two conjugate-center distance cutoffs. -/
def analyticDistance (z : ℂ) (l : Fin 45) : ℝ :=
  (max ‖z-analyticCenter l‖ (1/50))*(max ‖z-star (analyticCenter l)‖ (1/50))

theorem analyticDistance_lower (z : ℂ) (l : Fin 45) : 1/2500≤analyticDistance z l := by
  have h1 : (1/50:ℝ)≤max ‖z-analyticCenter l‖ (1/50) := le_max_right _ _
  have h2 : (1/50:ℝ)≤max ‖z-star (analyticCenter l)‖ (1/50) := le_max_right _ _
  have h := mul_le_mul h1 h2 (by norm_num : (0:ℝ)≤1/50) (by positivity)
  norm_num at h
  exact h

theorem analyticDistance_pos (z : ℂ) (l : Fin 45) : 0<analyticDistance z l :=
  lt_of_lt_of_le (by norm_num) (analyticDistance_lower z l)

theorem analyticDistance_log_lower (z : ℂ) (l : Fin 45) :
    -Real.log 2500≤Real.log (analyticDistance z l) := by
  have h := Real.log_le_log (by norm_num : (0:ℝ)<1/2500) (analyticDistance_lower z l)
  simpa [Real.log_div] using h

def analyticBasisPotential (w : Fin 45→ℝ) (z : ℂ) : ℝ :=
  ∑ l,w l*Real.log (analyticDistance z l)

theorem roundedBlock_log_bound (i : ℕ) (w : Fin 45→ℝ) (hw : ∀ l,0≤w l)
    (z : ℂ) (l : Fin 45) :
    (roundedBlockSize i w l:ℝ)*Real.log (analyticDistance z l) ≤
      ((i:ℝ)*w l/2)*Real.log (analyticDistance z l)+Real.log 2500 := by
  have hw0 := hw l
  have hfloor := Nat.floor_le (show 0≤(i:ℝ)*w l/2 by positivity)
  have hceil := Nat.lt_floor_add_one ((i:ℝ)*w l/2)
  change (roundedBlockSize i w l:ℝ)≤(i:ℝ)*w l/2 at hfloor
  change (i:ℝ)*w l/2<(roundedBlockSize i w l:ℝ)+1 at hceil
  have hlog := analyticDistance_log_lower z l
  have hC : 0≤Real.log (2500:ℝ) := Real.log_nonneg (by norm_num)
  have hprod := mul_nonneg (sub_nonneg.mpr hfloor) (sub_nonneg.mpr hlog)
  nlinarith

theorem roundedBlock_log_sum_bound (i : ℕ) (w : Fin 45→ℝ) (hw : ∀ l,0≤w l) (z : ℂ) :
    (∑ l : Fin 45,(roundedBlockSize i w l:ℝ)*Real.log (analyticDistance z l)) ≤
      (i:ℝ)/2*analyticBasisPotential w z+45*Real.log 2500 := by
  have h := Finset.sum_le_sum (fun l (_ : l∈Finset.univ) => roundedBlock_log_bound i w hw z l)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  have he : (∑ l : Fin 45,((i:ℝ)*w l/2)*Real.log (analyticDistance z l))=
      (i:ℝ)/2*analyticBasisPotential w z := by
    unfold analyticBasisPotential
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rwa [he] at h

theorem concreteAnalyticBasis_positive_majorant (i : ℕ) (w : Fin 45→ℝ) (z : ℂ) :
    ‖(concreteAnalyticBasis i w).eval z‖≤
      (1+‖z‖)^(roundedRemainder i w)*4^45*
        ∏ l : Fin 45,(analyticDistance z l)^(roundedBlockSize i w l) := by
  apply (concreteAnalyticBasis_eval_bound i w z).trans
  have hn : ‖z-1‖≤1+‖z‖ := by
    have := norm_sub_le z 1
    simpa [add_comm] using this
  dsimp [analyticDistance]
  gcongr

theorem concreteAnalyticBasis_log_bound (i : ℕ) (w : Fin 45→ℝ)
    (hw : ∀ l,0≤w l) (hs : ∑ l,w l=1) (z : ℂ)
    (hz : (concreteAnalyticBasis i w).eval z≠0) :
    Real.log ‖(concreteAnalyticBasis i w).eval z‖≤
      (i:ℝ)/2*analyticBasisPotential w z+45*Real.log 4+45*Real.log 2500+
        90*Real.log (1+‖z‖) := by
  have hbase : 0<1+‖z‖ := by positivity
  have hp : 0<(∏ l : Fin 45,(analyticDistance z l)^(roundedBlockSize i w l)) :=
    Finset.prod_pos (fun l _ => pow_pos (analyticDistance_pos z l) _)
  have h := Real.log_le_log (norm_pos_iff.mpr hz) (concreteAnalyticBasis_positive_majorant i w z)
  rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ hbase.ne') (by norm_num)) hp.ne',
    Real.log_mul (pow_ne_zero _ hbase.ne') (by norm_num),Real.log_pow,Real.log_pow,
    Real.log_prod (fun l _ => pow_ne_zero _ (analyticDistance_pos z l).ne')] at h
  simp only [Real.log_pow] at h
  have hs' := roundedBlock_log_sum_bound i w hw z
  have hd : (roundedRemainder i w:ℝ)≤90 := by
    exact_mod_cast (concreteAnalyticBasis_remainder_lt i w hw hs).le
  have hl : 0≤Real.log (1+‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
  have hdl := mul_le_mul_of_nonneg_right hd hl
  norm_num only [Nat.cast_ofNat] at h
  linarith
end OddZeta.FourValue

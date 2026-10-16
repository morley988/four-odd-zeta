import FourValueWeightLog

noncomputable section
namespace OddZeta.FourValue
open Polynomial

theorem analyticWeight_scaled_log_bound (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : 1<z.re) :
    Real.log ‖analyticZetaFunction n 1 ((100*(n:ℂ))*z)‖≤
      (100*(n:ℝ))*targetWeightPotential z-9*Real.log (100*(n:ℝ))+
      targetNormalizationLogCorrection+5/6+Real.log 2+Real.log ‖z‖+
      5*rootLogProfile z (-1)-∑ i : Fin 15,rootLogProfile z (targetAlpha i) := by
  let M : ℝ := 100*(n:ℝ)
  have hM : 0<M := by
    dsimp [M]
    have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    positivity
  have hMc : (M:ℂ)=100*(n:ℂ) := by simp [M]
  have hnlog := (abs_le.mp (targetNormalization_uniform_error n hn)).2
  have hnum := (centeredRoot_scaled_log_error (100*n) M hM z
    (by simpa [M,div_self hM.ne'] using hz)).2
  have ha (i : Fin 15) : (targetEndpointTuple n i:ℝ)/M=targetAlpha i := by
    rw [targetEndpointTuple_scaled]
    dsimp [M]
    field_simp
  have hden (i : Fin 15) := (centeredRoot_scaled_log_error (targetEndpointTuple n i) M hM z
    (by rw [ha]; linarith [(targetAlpha_bounds i).2])).1
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin 15) _ => hden i)
  simp_rw [ha] at hsum
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib] at hsum
  rw [← Finset.sum_mul,← Finset.mul_sum] at hsum
  have hdeg : ∑ i : Fin 15,(2*(targetEndpointTuple n i:ℝ)+1)=1722*(n:ℝ)+15 := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,targetEndpointTuple_sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    norm_num
    ring
  rw [hdeg] at hsum
  have hmdiv : ((100*n:ℕ):ℝ)/M=1 := by simp [M,div_self hM.ne']
  have hmneg : -((100*n:ℕ):ℝ)/M = -1 := by rw [neg_div,hmdiv]
  rw [hmdiv,hmneg] at hnum
  have hz0 : z≠0 := by intro he; norm_num [he] at hz
  have hlogz : Real.log ‖(M:ℂ)*z‖=Real.log M+Real.log ‖z‖ := by
    rw [norm_mul,Real.log_mul (by simpa using hM.ne') (norm_ne_zero_iff.mpr hz0)]
    simp [abs_of_pos hM]
  have hzre : 100*(n:ℝ)<((M:ℂ)*z).re := by
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    change M<M*z.re
    nlinarith
  have hid := analyticWeight_log_identity n ((M:ℂ)*z) hzre
  rw [hlogz] at hid
  rw [← hMc]
  unfold targetWeightPotential
  dsimp [M] at hnum hsum hid ⊢
  push_cast at hnum hsum hid ⊢
  linarith
end OddZeta.FourValue

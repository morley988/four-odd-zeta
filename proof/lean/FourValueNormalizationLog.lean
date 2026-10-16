import FourValueUniformStirling

noncomputable section
namespace OddZeta.FourValue
open Polynomial

def entropyTerm (x : ℝ) : ℝ := x*Real.log x-x

def targetNormalizationEntropy : ℝ :=
  (∑ i : Fin 10,entropyTerm (((2*targetFactorialEndpoints i:ℕ):ℝ)/100))-10*entropyTerm (33/100)

def targetNormalizationLogCorrection : ℝ :=
  (1/2)*(∑ i : Fin 10,Real.log (((2*targetFactorialEndpoints i:ℕ):ℝ)/100))-5*Real.log (33/100)

theorem targetFactorialEndpoints_positive (i : Fin 10) : 1≤targetFactorialEndpoints i := by
  fin_cases i <;> norm_num [targetFactorialEndpoints]

theorem targetFactorialEndpoints_sum : ∑ i : Fin 10,2*targetFactorialEndpoints i=1052 := by
  norm_num [targetFactorialEndpoints,Fin.sum_univ_succ]

theorem targetNormalization_log_norm (n : ℕ) :
    Real.log ‖targetNormalization (K:=ℂ) n‖=
      (∑ i : Fin 10,Real.log (Nat.factorial (2*targetFactorialEndpoints i*n):ℝ))-
        10*Real.log (Nat.factorial (33*n):ℝ) := by
  unfold targetNormalization
  rw [norm_div,norm_prod,norm_pow]
  simp only [Complex.norm_natCast]
  have hnum (i : Fin 10) : (Nat.factorial (2*targetFactorialEndpoints i*n):ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hden : (Nat.factorial (33*n):ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [Real.log_div (Finset.prod_ne_zero_iff.mpr (fun i _ => hnum i)) (pow_ne_zero 10 hden),
    Real.log_prod (fun i _ => hnum i),Real.log_pow]
  norm_num

theorem log_factorial_scaled_identity (m : ℕ) (M c : ℝ) (hM : 0<M) (hc : 0<c) (hm : (m:ℝ)=M*c) :
    Real.log (Nat.factorial m:ℝ)=
      (m:ℝ)*Real.log M+M*entropyTerm c+(1/2)*Real.log M+(1/2)*Real.log c+factorialLogRemainder m := by
  unfold factorialLogRemainder entropyTerm
  rw [hm,Real.log_mul hM.ne' hc.ne']
  ring

theorem targetNormalization_stirling_identity (n : ℕ) (hn : 1≤n) :
    Real.log ‖targetNormalization (K:=ℂ) n‖=
      722*(n:ℝ)*Real.log (100*(n:ℝ))+(100*(n:ℝ))*targetNormalizationEntropy+
      targetNormalizationLogCorrection+
      (∑ i : Fin 10,factorialLogRemainder (2*targetFactorialEndpoints i*n))-
        10*factorialLogRemainder (33*n) := by
  have hM : 0<100*(n:ℝ) := by
    have : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    positivity
  have hnum (i : Fin 10) := log_factorial_scaled_identity (2*targetFactorialEndpoints i*n)
    (100*(n:ℝ)) (((2*targetFactorialEndpoints i:ℕ):ℝ)/100) hM
    (by have := targetFactorialEndpoints_positive i; positivity)
    (by push_cast; ring)
  have hden := log_factorial_scaled_identity (33*n) (100*(n:ℝ)) (33/100) hM (by norm_num)
    (by push_cast; ring)
  rw [targetNormalization_log_norm]
  simp_rw [hnum,hden]
  unfold targetNormalizationEntropy targetNormalizationLogCorrection
  simp_rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul,← Finset.mul_sum]
  have hsum : (∑ i : Fin 10,(2*targetFactorialEndpoints i*n:ℕ):ℝ)=1052*(n:ℝ) := by
    rw [← Nat.cast_sum,← Finset.sum_mul,targetFactorialEndpoints_sum]
    push_cast
    rfl
  rw [hsum]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  push_cast
  simp only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
  simp_rw [← Finset.mul_sum]
  ring
theorem targetNormalization_uniform_error (n : ℕ) (hn : 1≤n) :
    |Real.log ‖targetNormalization (K:=ℂ) n‖-
      (722*(n:ℝ)*Real.log (100*(n:ℝ))+(100*(n:ℝ))*targetNormalizationEntropy+
        targetNormalizationLogCorrection)|≤5/6 := by
  have he (i : Fin 10) := factorialLogRemainder_bounds (2*targetFactorialEndpoints i*n)
    (by have := targetFactorialEndpoints_positive i; nlinarith)
  have hd := factorialLogRemainder_bounds (33*n) (by omega)
  have hl := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin 10) _ => (he i).1)
  have hu := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin 10) _ => (he i).2)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hl hu
  norm_num only [Nat.cast_ofNat] at hl hu
  rw [targetNormalization_stirling_identity n hn]
  apply abs_le.mpr
  constructor <;> linarith [hd.1,hd.2]
end OddZeta.FourValue

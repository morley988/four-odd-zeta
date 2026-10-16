import FourValueConcreteContourComplete

noncomputable section
namespace OddZeta.FourValue

theorem targetHankelDegree_linear_bound (n : ℕ) : targetHankelDegree n≤181*n := by
  unfold targetHankelDegree
  omega

theorem targetHankelSize_linear_bound (n : ℕ) (hn : 1≤n) : targetHankelDegree n+1≤182*n := by
  have := targetHankelDegree_linear_bound n
  omega

theorem analyticTransitionBase_polynomial_bound (n : ℕ) (hn : 1≤n) :
    analyticTransitionBase n≤(400*(n:ℝ))^4 := by
  have hm : ((targetHankelDegree n+1:ℕ):ℝ)≤182*(n:ℝ) := by exact_mod_cast targetHankelSize_linear_bound n hn
  have hn0 : (0:ℝ)≤n := by positivity
  unfold analyticTransitionBase analyticRootRadius
  push_cast at hm ⊢
  calc
    _ ≤ (182*(n:ℝ))^2*(4*(100*(n:ℝ))^2) := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg ((n:ℝ)^2)]

theorem actualAnalyticTransferFactor_ge_one (n : ℕ) (hn : 1≤n) : 1≤actualAnalyticTransferFactor n := by
  have hm : (1:ℝ)≤(targetHankelDegree n+1:ℕ) := by exact_mod_cast (show 1≤targetHankelDegree n+1 by omega)
  unfold actualAnalyticTransferFactor triangularTransferFactor
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hm) (one_le_pow₀ (by linarith)))
    (one_le_pow₀ (analyticTransitionBase_ge_one n hn))

theorem actualAnalyticTransferFactor_polynomial_power (n : ℕ) (hn : 1≤n) :
    actualAnalyticTransferFactor n≤(400*(n:ℝ))^(3300*n) := by
  let m := targetHankelDegree n
  let k := m+1-4
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hm : m≤181*n := targetHankelDegree_linear_bound n
  have hsize : (m+1:ℕ)≤182*n := targetHankelSize_linear_bound n hn
  have hmr : ((m+1:ℕ):ℝ)≤182*(n:ℝ) := by exact_mod_cast hsize
  have hD := analyticTransitionBase_polynomial_bound n hn
  have hbase : 1≤400*(n:ℝ) := by linarith
  have hcodim : m+1-k≤4 := by omega
  have hcodim_mul := Nat.mul_le_mul_right m hcodim
  have hD0 : 0≤analyticTransitionBase n := le_trans (by norm_num) (analyticTransitionBase_ge_one n hn)
  have hk : k≤m+1 := by dsimp [k]; omega
  have hexp : k+k+4*((m+1-k)*m)≤3300*n := by omega
  unfold actualAnalyticTransferFactor triangularTransferFactor
  change ((m+1:ℕ):ℝ)^k*(2*((m+1:ℕ):ℝ))^k*(analyticTransitionBase n)^((m+1-k)*m)≤_
  calc
    _ ≤ (400*(n:ℝ))^k*(400*(n:ℝ))^k*((400*(n:ℝ))^4)^((m+1-k)*m) := by
      have h1 := pow_le_pow_left₀ (show 0≤((m+1:ℕ):ℝ) by positivity)
        (show ((m+1:ℕ):ℝ)≤400*(n:ℝ) by linarith) k
      have h2 := pow_le_pow_left₀ (show 0≤2*((m+1:ℕ):ℝ) by positivity)
        (show 2*((m+1:ℕ):ℝ)≤400*(n:ℝ) by linarith) k
      have h3 := pow_le_pow_left₀ hD0 hD ((m+1-k)*m)
      exact mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)
    _ = (400*(n:ℝ))^(k+k+4*((m+1-k)*m)) := by rw [← pow_mul,← pow_add,← pow_add]
    _ ≤ _ := pow_le_pow_right₀ hbase hexp
end OddZeta.FourValue

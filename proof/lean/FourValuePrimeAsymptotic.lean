import PrimeNumberTheoremAnd.Consequences

open Filter Asymptotics
open scoped Topology Chebyshev
namespace OddZeta.FourValue.PrimeAsymptotic

/-- PNT+ supplies the actual Chebyshev asymptotic, not an axiom added by this project. -/
theorem theta_ratio_limit : Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 1) := by
  apply (isEquivalent_iff_tendsto_one ?_).mp chebyshev_asymptotic
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  exact ne_of_gt hx

theorem theta_scaled_limit (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => θ (c*x)/x) atTop (𝓝 c) := by
  have ht := theta_ratio_limit.comp ((tendsto_const_mul_atTop_of_pos hc).mpr tendsto_id)
  have ht' := ht.mul_const c
  have heq : (fun x : ℝ => (θ (c*x)/(c*x))*c) = (fun x : ℝ => θ (c*x)/x) := by
    ext x
    by_cases hx : x=0
    · simp [hx]
    · field_simp [ne_of_gt hc]
  simpa only [Function.comp_def, id_eq, one_mul, heq] using ht'

/-- Logarithmic prime mass on fixed dilated intervals. -/
theorem prime_interval_limit (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun x : ℝ => (θ (b*x)-θ (a*x))/x) atTop (𝓝 (b-a)) := by
  simpa only [sub_div] using (theta_scaled_limit b hb).sub (theta_scaled_limit a ha)

/-- Finite step weights, the building blocks of the prime correction. -/
theorem weighted_prime_intervals {ι : Type*} [Fintype ι] (w a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    Tendsto (fun x : ℝ => ∑ i, w i*((θ (b i*x)-θ (a i*x))/x))
      atTop (𝓝 (∑ i, w i*(b i-a i))) := by
  apply tendsto_finsetSum
  intro i _
  exact (prime_interval_limit (a i) (b i) (ha i) (hb i)).const_mul (w i)


theorem psi_ratio_limit : Tendsto (fun x : ℝ => ψ x / x) atTop (𝓝 1) := by
  apply (isEquivalent_iff_tendsto_one ?_).mp WeakPNT''
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  exact ne_of_gt hx

theorem psi_scaled_limit (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => ψ (c*x)/x) atTop (𝓝 c) := by
  have ht := psi_ratio_limit.comp ((tendsto_const_mul_atTop_of_pos hc).mpr tendsto_id)
  have ht' := ht.mul_const c
  have heq : (fun x : ℝ => (ψ (c*x)/(c*x))*c) = (fun x : ℝ => ψ (c*x)/x) := by
    ext x
    by_cases hx : x=0
    · simp [hx]
    · field_simp [ne_of_gt hc]
  simpa only [Function.comp_def, id_eq, one_mul, heq] using ht'

/-- Higher prime powers have no linear contribution. -/
theorem higher_power_limit (c : ℝ) (hc : 0<c) :
 Tendsto (fun x : ℝ => (ψ (c*x)-θ (c*x))/x) atTop (𝓝 0) := by
 simpa only [sub_div,sub_self] using (psi_scaled_limit c hc).sub (theta_scaled_limit c hc)

theorem weighted_prime_intervals_nat {ι : Type*} [Fintype ι] (w a b : ι → ℝ)
 (ha : ∀i,0<a i) (hb : ∀i,0<b i) :
 Tendsto (fun n : ℕ => ∑i,w i*((θ (b i*n)-θ (a i*n))/(n:ℝ)))
   atTop (𝓝 (∑i,w i*(b i-a i))) :=
 (weighted_prime_intervals w a b ha hb).comp tendsto_natCast_atTop_atTop

#print axioms higher_power_limit
#print axioms chebyshev_asymptotic
#print axioms weighted_prime_intervals
end OddZeta.FourValue.PrimeAsymptotic

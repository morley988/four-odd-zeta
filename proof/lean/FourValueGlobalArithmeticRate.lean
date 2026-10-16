import FourValueGlobalPrimeSum

noncomputable section
namespace OddZeta.FourValue.ArithmeticCertificate
open Filter Corrected Finset
open scoped Topology Chebyshev

def Grid.rate (G : Grid) : ℝ :=
 ((∑i,((G.cell i).hi-(G.cell i).lo)*(G.cell i).lower:ℚ):ℝ)/10000-361/10000

theorem Grid.logBound_limit (G : Grid) (hG : G.Valid) (Q : ℕ) :
 Tendsto (fun n : ℕ => G.logBound n Q/(100*(n:ℝ))^2) atTop (𝓝 G.rate) := by
 have ha (i : Fin G.count) : (0:ℝ)<(G.cell i).lo := by
   have hh : (0:ℚ)<(G.cell i).lo := lt_of_lt_of_le (by norm_num) (hG.cells i).2.2.lo_pos
   exact_mod_cast hh
 have hb (i : Fin G.count) : (0:ℝ)<(G.cell i).hi :=
   (ha i).trans (by exact_mod_cast (hG.cells i).2.2.lt)
 have ht := PrimeAsymptotic.weighted_prime_intervals_nat
   (fun i => ((G.cell i).lower:ℝ)) (fun i => ((G.cell i).lo:ℝ))
   (fun i => ((G.cell i).hi:ℝ)) ha hb
 have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
   tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
 have htheta := (PrimeAsymptotic.theta_scaled_limit 361 (by norm_num)).comp tendsto_natCast_atTop_atTop
 have he := ((ht.div_const 10000).sub ((htheta.mul hi).const_mul ((G.error:ℝ)/10000))).sub
   smallPrimeEnvelope_limit
 have hh := he.sub ((analyticMinorSize_ratio_limit.mul hi).const_mul (Real.log (Q:ℝ)/10000))
 convert hh using 1
 · ext n
   simp only [Grid.logBound,Grid.primeSum,Function.comp_def]
   rw [show (∑i,((G.cell i).lower:ℝ)*((θ (((G.cell i).hi:ℝ)*n)-θ (((G.cell i).lo:ℝ)*n))/(n:ℝ)))=
     (∑i,((G.cell i).lower:ℝ)*(θ (((G.cell i).hi:ℝ)*n)-θ (((G.cell i).lo:ℝ)*n)))/(n:ℝ) by
       simp only [mul_div_assoc,sum_div]]
   by_cases hn : n=0
   · simp [hn]
   · have hnR : (n:ℝ)≠0 := by exact_mod_cast hn
     field_simp
     <;> ring
 · simp only [mul_zero,zero_mul,sub_zero,Grid.rate,Rat.cast_sum,Rat.cast_mul,Rat.cast_sub]
   congr 2
   congr 1
   apply sum_congr rfl
   intros
   ring

theorem Grid.rate_gt_target (G : Grid) (hG : G.Valid) : (-288/25:ℝ)<G.rate := by
 have hh : (-114800:ℝ)≤((∑i,((G.cell i).hi-(G.cell i).lo)*(G.cell i).lower:ℚ):ℝ) := by exact_mod_cast hG.integral
 unfold Grid.rate
 linarith

theorem Grid.eventual_log_lower (G : Grid) (hG : G.Valid) (z : Fin 4 → ℚ) :
 ∀ᶠ n : ℕ in atTop,
 ∀ (rows cols : Fin (analyticMinorSize n) ↪ Fin (targetHankelDegree n+1)),
 ((Corrected.rationalFourValueMatrix n z).submatrix rows cols).det≠0 →
 (100*(n:ℝ))^2*(-288/25)≤Real.log |(((Corrected.rationalFourValueMatrix n z).submatrix rows cols).det:ℝ)| := by
 have hh := (G.logBound_limit hG (rationalPencilDenominator z)).eventually
   (eventually_gt_nhds (G.rate_gt_target hG))
 filter_upwards [hh,eventually_ge_atTop (320000:ℕ),
   eventually_ge_atTop (20*rationalPencilDenominator z)] with n hn hn0 hnQ
 intro rows cols hq
 have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
 have hd : (0:ℝ)<(100*(n:ℝ))^2 := by positivity
 have hlow := (lt_div_iff₀ hd).mp hn
 have hlog := G.log_bound hG n z hn0 hnQ rows cols hq
 nlinarith

#print axioms Grid.eventual_log_lower
end OddZeta.FourValue.ArithmeticCertificate

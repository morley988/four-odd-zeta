import FourValueExternalArithmetic

noncomputable section
namespace OddZeta.FourValue.FullGrid
open OddZeta.FourValue.Transcendental
open Filter
open scoped Topology

theorem g_bound (k : Fin 50000) :
 certificateG (right k:ℝ)-2*Real.pi*(right k:ℝ)+cellSlope*(1/10000) ≤ (G k:ℝ) := by
 rw [← gExpr_eval]
 exact ((gExpr k).contains (expression_rows k)).2.trans (Rat.cast_le.mpr (expression_upper k))

theorem log_bound (k : Fin 50000) (j : Fin 45) :
 Real.log ((U k j:ℝ)+(34/25)*(5/50000)^2/4)+
 Real.log ((V k j:ℝ)+(34/25)*(5/50000)^2/4) ≤ (K k j:ℝ) := by
 have hu : uRow k j < External.logCount := by
   have := k.isLt; have := j.isLt; dsimp [uRow,External.logCount]; omega
 have hv : vRow k j < External.logCount := by
   have := k.isLt; have := j.isLt; dsimp [vRow,uRow,External.logCount]; omega
 have a := (External.log_values ⟨uRow k j,hu⟩).2
 have b := (External.log_values ⟨vRow k j,hv⟩).2
 have c : ((External.upper (uRow k j)+External.upper (vRow k j):ℚ):ℝ) ≤ (K k j:ℝ) := Rat.cast_le.mpr (pair_upper k j)
 have eu : (U k j:ℝ)+(34/25)*(5/50000)^2/4 = (External.argument (uRow k j):ℝ) := by
   simp [U]; ring
 have ev : (V k j:ℝ)+(34/25)*(5/50000)^2/4 = (External.argument (vRow k j):ℝ) := by
   simp [V]; ring
 rw [eu,ev]
 exact (add_le_add a b).trans (by simpa only [Rat.cast_add] using c)

theorem left_cast (k : Fin 50000) : (left k:ℝ)=(k:ℕ)*(5/50000) := by
 simp [left]; ring
theorem right_cast (k : Fin 50000) : (right k:ℝ)=((k:ℕ)+1)*(5/50000) := by
 simp [right]; ring

/-- Full grid, assembled from scalar enclosures and finite rational checks. -/
def certificate : GridCertificate 50000 where
 count_pos := by norm_num
 G k := G k
 K k j := K k j
 U k j := U k j
 V k j := V k j
 g_bound k := by simpa only [Nat.cast_ofNat,right_cast,show (1/10000:ℝ)=5/50000 by norm_num] using g_bound k
 u_left k j := by
   have h := distances k j
   simpa only [Nat.cast_ofNat,left_cast] using Batch.distance_checked (left k) (U k j) j (by linarith [h.1]) h.2.2.1
 u_right k j := by
   have h := distances k j
   simpa only [Nat.cast_ofNat,right_cast] using Batch.distance_checked (right k) (U k j) j (by linarith [h.1]) h.2.2.2.1
 v_left k j := by
   have h := distances k j
   simpa only [Nat.cast_ofNat,left_cast] using Batch.conjugate_distance_checked (left k) (V k j) j (by linarith [h.2.1]) h.2.2.2.2.1
 v_right k j := by
   have h := distances k j
   simpa only [Nat.cast_ofNat,right_cast] using Batch.conjugate_distance_checked (right k) (V k j) j (by linarith [h.2.1]) h.2.2.2.2.2
 u_cutoff k j := by
   have h : ((1/50:ℚ):ℝ) ≤ (U k j:ℝ) := Rat.cast_le.mpr (distances k j).1
   norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
   exact h
 v_cutoff k j := by
   have h : ((1/50:ℚ):ℝ) ≤ (V k j:ℝ) := Rat.cast_le.mpr (distances k j).2.1
   norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
   exact h
 log_bound := log_bound
 knot_bound k := Batch.knots_checked (G k) (K k) (knot_arithmetic k)

theorem finite_knots : Numerical.FiniteKnotCertificate := finite_certificate_of_grid certificate

theorem all_knots : Numerical.KnotCertificate := Numerical.knotCertificate_of_finite finite_knots

theorem envelope_bound (s y : ℝ) (hs : 0≤s) (hs1 : s≤basisLimit) (hy : 0<y) :
 certificateG y-2*Real.pi*y+
 s*analyticBasisPotential (concreteBasisWeight s) ((normalizedContourPoint y)^2) ≤ Numerical.envelope s :=
 Numerical.pointwise_of_knots all_knots s y hs hs1 hy

/-- The numerical certificate hypothesis is discharged, conditional only on the
seven explicitly marked finite external calculation families. -/
theorem numerical_rate :
 ∃ E : ℕ→ℝ,
 Tendsto (fun n : ℕ => E n/(n:ℝ)^2) atTop (𝓝 0) ∧
 ∀ n : ℕ,1≤n → ∀ rows cols : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1),
 ‖((analyticZetaMatrix n).submatrix rows cols).det‖≤
 Real.exp ((100*(n:ℝ))^2*(-577853339/50000000)+E n) :=
 Numerical.numerical_rate_of_finite_certificate finite_knots

end OddZeta.FourValue.FullGrid

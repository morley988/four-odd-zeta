import FourValueTranscendentalCells
import FourValueNumericalCells
import FourValueNumericalBridge

noncomputable section
namespace OddZeta.FourValue.Transcendental
open Finset

theorem grid_cover (N : ℕ) (d y : ℝ) (hd : 0 < d) (hy : 0 < y) (hyN : y ≤ N*d) :
    ∃ k : Fin N, (k:ℝ)*d ≤ y ∧ y ≤ ((k:ℕ)+1:ℝ)*d := by
  induction N with
  | zero => simp only [Nat.cast_zero, zero_mul] at hyN; linarith
  | succ N ih =>
    by_cases h : y ≤ (N:ℝ)*d
    · obtain ⟨k, hk0, hk1⟩ := ih h
      exact ⟨⟨k, Nat.lt_trans k.isLt (Nat.lt_succ_self N)⟩, hk0, hk1⟩
    · refine ⟨⟨N, Nat.lt_succ_self N⟩, le_of_lt (lt_of_not_ge h), ?_⟩
      simpa using hyN

/-- Finite endpoint data and its proof obligations. No field quantifies over a height interval. -/
structure GridCertificate (N : ℕ) where
  count_pos : 0 < N
  G : Fin N → ℝ
  K : Fin N → Fin 45 → ℝ
  U : Fin N → Fin 45 → ℝ
  V : Fin N → Fin 45 → ℝ
  g_bound : ∀ k : Fin N,
    certificateG (((k:ℕ)+1:ℝ)*(5/N))-2*Real.pi*(((k:ℕ)+1:ℝ)*(5/N))+
      cellSlope*(5/N) ≤ G k
  u_left : ∀ (k : Fin N) (j : Fin 45), ‖(normalizedContourPoint ((k:ℝ)*(5/N)))^2-analyticCenter j‖ ≤ U k j
  u_right : ∀ (k : Fin N) (j : Fin 45), ‖(normalizedContourPoint (((k:ℕ)+1:ℝ)*(5/N)))^2-analyticCenter j‖ ≤ U k j
  v_left : ∀ (k : Fin N) (j : Fin 45), ‖(normalizedContourPoint ((k:ℝ)*(5/N)))^2-star (analyticCenter j)‖ ≤ V k j
  v_right : ∀ (k : Fin N) (j : Fin 45), ‖(normalizedContourPoint (((k:ℕ)+1:ℝ)*(5/N)))^2-star (analyticCenter j)‖ ≤ V k j
  u_cutoff : ∀ (k : Fin N) (j : Fin 45), (1/50:ℝ) ≤ U k j
  v_cutoff : ∀ (k : Fin N) (j : Fin 45), (1/50:ℝ) ≤ V k j
  log_bound : ∀ (k : Fin N) (j : Fin 45),
    Real.log (U k j+(34/25:ℝ)*(5/N)^2/4)+
      Real.log (V k j+(34/25:ℝ)*(5/N)^2/4) ≤ K k j
  knot_bound : ∀ (k : Fin N) (m : ℕ), m ≤ 41 →
    G k+basisKnot m*(∑ j, basisKnotWeight m j*K k j) ≤ Numerical.height m

theorem finite_certificate_of_grid {N : ℕ} (D : GridCertificate N) :
    Numerical.FiniteKnotCertificate := by
  intro m hm y hy hy5
  have hN : (0:ℝ) < N := by exact_mod_cast D.count_pos
  let d : ℝ := 5/N
  have hd : 0 < d := div_pos (by norm_num) hN
  have hNd : (N:ℝ)*d = 5 := by dsimp [d]; field_simp
  obtain ⟨k, hleft, hright⟩ := grid_cover N d y hd hy (by rwa [hNd])
  let l : ℝ := (k:ℝ)*d
  let h : ℝ := ((k:ℕ)+1:ℝ)*d
  let t : ℝ := (y-l)/d
  have hwidth : h-l=d := by dsimp [h,l]; ring
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hleft) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).mpr (by dsimp [l,h] at *; linarith)
  have he : (1-t)*l+t*h=y := by dsimp [t]; rw [show (1-(y-l)/d)*l+(y-l)/d*h = l+(y-l)/d*(h-l) by ring, hwidth]; field_simp; ring
  have hg : certificateG y-2*Real.pi*y ≤ D.G k := by
    apply (certificateG_cell y h d hy hright (by linarith)).trans
    exact D.g_bound k
  have hb (j : Fin 45) : Real.log (analyticDistance ((normalizedContourPoint y)^2) j) ≤ D.K k j := by
    have hcell := Numerical.basis_log_cell_bound l h t ht ht1 j (D.U k j) (D.V k j)
      (D.u_left k j) (D.u_right k j) (D.v_left k j) (D.v_right k j)
      (D.u_cutoff k j) (D.v_cutoff k j)
    rw [he, hwidth] at hcell
    exact hcell.trans (D.log_bound k j)
  have hs : analyticBasisPotential (basisKnotWeight m) ((normalizedContourPoint y)^2) ≤
      ∑ j, basisKnotWeight m j*D.K k j := by
    apply sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hb j) (certificateWeight_nonneg _ j)
  exact (add_le_add hg (mul_le_mul_of_nonneg_left hs (basisKnot_nonneg m))).trans (D.knot_bound k m hm)

end OddZeta.FourValue.Transcendental

import FourValueFastReduction
import FourValueTranscendentalChecks
import FourValueTranscendentalGrid

noncomputable section
namespace OddZeta.FourValue.Batch
open OddZeta.FourValue.Transcendental QInterval

def piBox : QInterval := ⟨314159265358979323844/10^20,314159265358979323864/10^20⟩

theorem piBox_contains : piBox.Contains Real.pi := by
  have h := pi_machin_enclosure
  norm_num [piBox,QInterval.Contains] at h ⊢
  exact h

theorem log_checked (q lo hi : ℚ)
    (h : (Fast.reducedLogInterval (2^80) 24 64 q).any
      (fun a => decide (lo ≤ a.lo ∧ a.hi ≤ hi)) = true) :
    (lo:ℝ) ≤ Real.log (q:ℝ) ∧ Real.log (q:ℝ) ≤ (hi:ℝ) := by
  cases he : Fast.reducedLogInterval (2^80) 24 64 q with
  | none => simp only [he,Option.any_none,Bool.false_eq_true] at h
  | some a =>
    simp only [he,Option.any_some,decide_eq_true_eq] at h
    have ha := Fast.reducedLogInterval_contains (2^80) 24 (by positivity) 64 q a he
    have hl : (lo:ℝ) ≤ (a.lo:ℝ) := by exact_mod_cast h.1
    have hu : (a.hi:ℝ) ≤ (hi:ℝ) := by exact_mod_cast h.2
    exact ⟨hl.trans ha.1,ha.2.trans hu⟩

theorem atan_checked (q lo hi : ℚ)
    (h : lo ≤ (Fast.atanInterval (2^80) 32 piBox q).lo ∧
      (Fast.atanInterval (2^80) 32 piBox q).hi ≤ hi) :
    (lo:ℝ) ≤ Real.arctan (q:ℝ) ∧ Real.arctan (q:ℝ) ≤ (hi:ℝ) := by
  have ha := Fast.atanInterval_contains (2^80) 32 (by positivity) piBox piBox_contains q
  have hl : (lo:ℝ) ≤ ((Fast.atanInterval (2^80) 32 piBox q).lo:ℝ) := by exact_mod_cast h.1
  have hu : ((Fast.atanInterval (2^80) 32 piBox q).hi:ℝ) ≤ (hi:ℝ) := by exact_mod_cast h.2
  exact ⟨hl.trans ha.1,ha.2.trans hu⟩

def pairCheck (u v k : ℚ) : Bool :=
  (Fast.reducedLogInterval (2^80) 24 64 u).any (fun a =>
    (Fast.reducedLogInterval (2^80) 24 64 v).any (fun b => decide (a.hi+b.hi ≤ k)))

theorem pair_checked (u v k : ℚ) (h : pairCheck u v k = true) :
    Real.log (u:ℝ)+Real.log (v:ℝ) ≤ (k:ℝ) := by
  unfold pairCheck at h
  cases he : Fast.reducedLogInterval (2^80) 24 64 u with
  | none => simp only [he,Option.any_none,Bool.false_eq_true] at h
  | some a =>
    simp only [he,Option.any_some] at h
    cases hf : Fast.reducedLogInterval (2^80) 24 64 v with
    | none => simp only [hf,Option.any_none,Bool.false_eq_true] at h
    | some b =>
      simp only [hf,Option.any_some,decide_eq_true_eq] at h
      have ha := Fast.reducedLogInterval_contains (2^80) 24 (by positivity) 64 u a he
      have hb := Fast.reducedLogInterval_contains (2^80) 24 (by positivity) 64 v b hf
      have hh : (a.hi:ℝ)+(b.hi:ℝ) ≤ (k:ℝ) := by exact_mod_cast h
      exact (add_le_add ha.2 hb.2).trans hh

theorem norm_le_of_squares (z : ℂ) (u : ℝ) (hu : 0 ≤ u)
    (hs : z.re^2+z.im^2 ≤ u^2) : ‖z‖ ≤ u := by
  have h := Complex.sq_norm z
  simp only [Complex.normSq_apply] at h
  nlinarith [norm_nonneg z]

def centerq (j : Fin 45) : ℚ × ℚ := Certificate.centers.get ⟨j.val,by simpa [Certificate.center_count] using j.isLt⟩
def zr (t : ℚ) : ℚ := 1+(6/5)*t-(16/25)*t^2
def zi (t : ℚ) : ℚ := 2*t+(6/5)*t^2

theorem distance_checked (t u : ℚ) (j : Fin 45) (hu : 0 ≤ u)
    (hs : (zr t-(centerq j).1)^2+(zi t-(centerq j).2)^2 ≤ u^2) :
    ‖(normalizedContourPoint (t:ℝ))^2-analyticCenter j‖ ≤ (u:ℝ) := by
  apply norm_le_of_squares _ _ (by exact_mod_cast hu)
  have hs' : (((zr t-(centerq j).1)^2+(zi t-(centerq j).2)^2:ℚ):ℝ) ≤ ((u^2:ℚ):ℝ) := Rat.cast_le.mpr hs
  convert hs' using 1 <;> simp [zr,zi,centerq,normalizedContourPoint,analyticCenter,pow_two,Complex.mul_re,Complex.mul_im] <;> push_cast <;> ring

theorem conjugate_distance_checked (t u : ℚ) (j : Fin 45) (hu : 0 ≤ u)
    (hs : (zr t-(centerq j).1)^2+(zi t+(centerq j).2)^2 ≤ u^2) :
    ‖(normalizedContourPoint (t:ℝ))^2-star (analyticCenter j)‖ ≤ (u:ℝ) := by
  apply norm_le_of_squares _ _ (by exact_mod_cast hu)
  have hs' : (((zr t-(centerq j).1)^2+(zi t+(centerq j).2)^2:ℚ):ℝ) ≤ ((u^2:ℚ):ℝ) := Rat.cast_le.mpr hs
  convert hs' using 1 <;> simp [zr,zi,centerq,normalizedContourPoint,analyticCenter,pow_two,Complex.mul_re,Complex.mul_im] <;> push_cast <;> ring

def knotq (m : ℕ) : ℚ := if m=0 then 0 else if m=41 then 361/200 else (361/200)*(2*(m:ℚ)-1)/80

def weightq (m : ℕ) (j : Fin 45) : ℚ :=
  ((certificateWeightRow ⟨min (m-1) 39,by omega⟩).get ⟨j.val,by rw [certificateWeightRow_length];exact j.isLt⟩:ℚ)/100000000

def heightq (m : ℕ) : ℚ := (Certificate.knotBounds.getD m (0,0)).2

theorem knotq_cast (m : ℕ) : (knotq m:ℝ)=basisKnot m := by
  unfold knotq basisKnot basisLimit
  split_ifs <;> push_cast <;> rfl

theorem weightq_cast (m : ℕ) (j : Fin 45) : (weightq m j:ℝ)=basisKnotWeight m j := by
  simp [weightq,basisKnotWeight,certificateWeight]

theorem knots_checked (g : ℚ) (ks : Fin 45 → ℚ)
    (hc : ∀ m : Fin 42, g+knotq m*(∑ j,weightq m j*ks j) ≤ heightq m) :
    ∀ m, m ≤ 41 → (g:ℝ)+basisKnot m*(∑ j,basisKnotWeight m j*(ks j:ℝ)) ≤ Numerical.height m := by
  intro m hm
  have h := hc ⟨m,by omega⟩
  have hr : ((g+knotq m*(∑ j,weightq m j*ks j):ℚ):ℝ) ≤ (heightq m:ℝ) := Rat.cast_le.mpr h
  push_cast at hr
  simpa only [knotq_cast,weightq_cast,heightq,Numerical.height] using hr

structure CellCertificate (l h : ℝ) where
  width_pos : l < h
  G : ℝ
  K : Fin 45 → ℝ
  U : Fin 45 → ℝ
  V : Fin 45 → ℝ
  g_bound : certificateG h-2*Real.pi*h+cellSlope*(h-l) ≤ G
  u_left : ∀ j, ‖(normalizedContourPoint l)^2-analyticCenter j‖ ≤ U j
  u_right : ∀ j, ‖(normalizedContourPoint h)^2-analyticCenter j‖ ≤ U j
  v_left : ∀ j, ‖(normalizedContourPoint l)^2-star (analyticCenter j)‖ ≤ V j
  v_right : ∀ j, ‖(normalizedContourPoint h)^2-star (analyticCenter j)‖ ≤ V j
  u_cutoff : ∀ j, (1/50:ℝ) ≤ U j
  v_cutoff : ∀ j, (1/50:ℝ) ≤ V j
  log_bound : ∀ j, Real.log (U j+(34/25)*(h-l)^2/4)+Real.log (V j+(34/25)*(h-l)^2/4) ≤ K j
  knot_bound : ∀ m, m ≤ 41 → G+basisKnot m*(∑ j, basisKnotWeight m j*K j) ≤ Numerical.height m

theorem cell_certificate_sound {l h : ℝ} (D : CellCertificate l h) (m : ℕ) (hm : m ≤ 41)
    (y : ℝ) (hy : 0 < y) (hl : l ≤ y) (hh : y ≤ h) :
    certificateG y-2*Real.pi*y+
      basisKnot m*analyticBasisPotential (basisKnotWeight m) ((normalizedContourPoint y)^2) ≤ Numerical.height m := by
  let t := (y-l)/(h-l)
  have hd : 0 < h-l := sub_pos.mpr D.width_pos
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hl) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith)
  have he : (1-t)*l+t*h=y := by dsimp [t]; field_simp; ring
  have hg := (certificateG_cell y h (h-l) hy hh (by linarith)).trans D.g_bound
  have hb (j : Fin 45) : Real.log (analyticDistance ((normalizedContourPoint y)^2) j) ≤ D.K j := by
    have hc := Numerical.basis_log_cell_bound l h t ht ht1 j (D.U j) (D.V j)
      (D.u_left j) (D.u_right j) (D.v_left j) (D.v_right j) (D.u_cutoff j) (D.v_cutoff j)
    rw [he] at hc
    exact hc.trans (D.log_bound j)
  have hs : analyticBasisPotential (basisKnotWeight m) ((normalizedContourPoint y)^2) ≤
      ∑ j, basisKnotWeight m j*D.K j := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hb j) (certificateWeight_nonneg _ j)
  exact (add_le_add hg (mul_le_mul_of_nonneg_left hs (basisKnot_nonneg m))).trans (D.knot_bound m hm)

end OddZeta.FourValue.Batch

import FourValueCertificate
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
namespace OddZeta.FourValue.Numerical
open MeasureTheory Set

/-- A clipped linear ramp, used to express the certificate interpolant. -/
def ramp (a b x : ℝ) : ℝ := min (max (x-a) 0) (b-a)

theorem ramp_continuous (a b : ℝ) : Continuous (ramp a b) := by
  unfold ramp
  fun_prop

theorem ramp_left (a b x : ℝ) (hab : a≤b) (hx : x≤a) : ramp a b x=0 := by
  simp [ramp,max_eq_right (sub_nonpos.mpr hx),min_eq_left (sub_nonneg.mpr hab)]

theorem ramp_middle (a b x : ℝ) (ha : a≤x) (hb : x≤b) : ramp a b x=x-a := by
  simp [ramp,max_eq_left (sub_nonneg.mpr ha),min_eq_left (sub_le_sub_right hb a)]

theorem ramp_right (a b x : ℝ) (hab : a≤b) (hx : b≤x) : ramp a b x=b-a := by
  rw [ramp,max_eq_left (sub_nonneg.mpr (hab.trans hx)),min_eq_right (sub_le_sub_right hx a)]

theorem ramp_integral (a b C : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤C) :
    (∫ x in 0..C,ramp a b x)=(b-a)*(C-(a+b)/2) := by
  have h0 : (∫ x in 0..a,ramp a b x)=0 := by
    calc
      _ = ∫ x in 0..a,(0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le ha] at hx
        exact ramp_left a b x hab hx.2
      _ = 0 := by simp
  have h1 : (∫ x in a..b,ramp a b x)=(b-a)^2/2 := by
    calc
      _ = ∫ x in a..b,x-a := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hab] at hx
        exact ramp_middle a b x hx.1 hx.2
      _ = (b-a)^2/2 := by
        rw [intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => a) (continuous_id.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _),integral_id,intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  have h2 : (∫ x in b..C,ramp a b x)=(C-b)*(b-a) := by
    calc
      _ = ∫ x in b..C,b-a := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hb] at hx
        exact ramp_right a b x hab hx.1
      _ = _ := by rw [intervalIntegral.integral_const]; rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((ramp_continuous a b).intervalIntegrable 0 a)
    ((ramp_continuous a b).intervalIntegrable a C)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((ramp_continuous a b).intervalIntegrable a b)
    ((ramp_continuous a b).intervalIntegrable b C)]
  rw [h0,h1,h2]
  ring

/-- Each edge stores its endpoints and its two heights. -/
def edgeTerm (a b : ℚ×ℚ) (x : ℝ) : ℝ :=
  ((b.2-a.2)/(b.1-a.1):ℚ)*ramp a.1 b.1 x

def edgeIntegral (C : ℚ) (a b : ℚ×ℚ) : ℚ :=
  (b.2-a.2)*(C-(a.1+b.1)/2)

def edges : List (ℚ×ℚ) → List ((ℚ×ℚ)×(ℚ×ℚ))
  | a::b::rest => (a,b)::edges (b::rest)
  | _ => []

def envelope (x : ℝ) : ℝ :=
  (-2396169/500000:ℝ)+( (edges Certificate.knotBounds).map
    (fun e => edgeTerm e.1 e.2 x)).sum

theorem edgeTerm_continuous (a b : ℚ×ℚ) : Continuous (edgeTerm a b) := by
  exact continuous_const.mul (ramp_continuous _ _)

theorem envelope_continuous : Continuous envelope := by
  unfold envelope
  apply continuous_const.add
  induction edges Certificate.knotBounds with
  | nil => simpa using (continuous_const : Continuous (fun _ : ℝ => (0:ℝ)))
  | cons a rest ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Continuous.add (edgeTerm_continuous a.1 a.2) ih

theorem edgeTerm_integral (C : ℚ) (a b : ℚ×ℚ) (ha : 0≤a.1)
    (hab : a.1<b.1) (hb : b.1≤C) :
    (∫ x in 0..(C:ℝ),edgeTerm a b x)=(edgeIntegral C a b:ℝ) := by
  unfold edgeTerm
  rw [intervalIntegral.integral_const_mul]
  rw [ramp_integral _ _ _ (by exact_mod_cast ha) (by exact_mod_cast hab.le) (by exact_mod_cast hb)]
  have hne : (b.1:ℝ)-(a.1:ℝ)≠0 := sub_ne_zero.mpr (by exact_mod_cast hab.ne')
  push_cast
  unfold edgeIntegral
  push_cast
  field_simp


theorem certificate_edges_valid : ∀ e ∈ edges Certificate.knotBounds,
    0≤e.1.1 ∧ e.1.1<e.2.1 ∧ e.2.1≤(361/200:ℚ) := by
  norm_num [edges,Certificate.knotBounds]

theorem edge_sum_integral (C : ℚ) (es : List ((ℚ×ℚ)×(ℚ×ℚ)))
    (h : ∀ e∈es,0≤e.1.1 ∧ e.1.1<e.2.1 ∧ e.2.1≤C) :
    (∫ x in 0..(C:ℝ),(es.map (fun e => edgeTerm e.1 e.2 x)).sum)=
      ((es.map (fun e => edgeIntegral C e.1 e.2)).sum:ℚ) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := h e (by simp)
    have ht : ∀ e∈es,0≤e.1.1 ∧ e.1.1<e.2.1 ∧ e.2.1≤C := by
      intro e he; exact h e (by simp [he])
    have hc : Continuous (fun x : ℝ => (es.map (fun e => edgeTerm e.1 e.2 x)).sum) := by
      clear h ht ih he
      induction es with
      | nil => simpa using (continuous_const : Continuous (fun _ : ℝ => (0:ℝ)))
      | cons a rest hi =>
        simp only [List.map_cons,List.sum_cons]
        exact Continuous.add (edgeTerm_continuous a.1 a.2) hi
    simp only [List.map_cons,List.sum_cons,Rat.cast_add]
    rw [intervalIntegral.integral_add ((edgeTerm_continuous e.1 e.2).intervalIntegrable _ _)
      (hc.intervalIntegrable _ _),edgeTerm_integral C e.1 e.2 he.1 he.2.1 he.2.2,ih ht]

theorem envelope_integral : (∫ x in 0..(361/200:ℝ),envelope x)=
    (-13277632257660676586509793/1024000000000000000000000:ℝ) := by
  unfold envelope
  have hc : Continuous (fun x : ℝ => ((edges Certificate.knotBounds).map
      (fun e => edgeTerm e.1 e.2 x)).sum) := by
    induction edges Certificate.knotBounds with
    | nil => simpa using (continuous_const : Continuous (fun _ : ℝ => (0:ℝ)))
    | cons a rest ih =>
      simp only [List.map_cons,List.sum_cons]
      exact Continuous.add (edgeTerm_continuous a.1 a.2) ih
  rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _),intervalIntegral.integral_const]
  have hi := edge_sum_integral (361/200) _ certificate_edges_valid
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hi
  rw [hi]
  norm_num [edges,Certificate.knotBounds,edgeIntegral]

end OddZeta.FourValue.Numerical

import FourValueNumericalSegments
import FourValueNumericalTail
import FourValueUniformAnalysisComplete
noncomputable section
namespace OddZeta.FourValue.Numerical
open MeasureTheory Set Filter
open scoped Topology
set_option maxHeartbeats 8000000
def height (k : ℕ) : ℝ := ((Certificate.knotBounds.getD k (0,0)).2:ℝ)

theorem height_lower (k : ℕ) (hk : k≤41) : (-9:ℝ)≤height k := by
  interval_cases k <;> norm_num [height,Certificate.knotBounds]

theorem envelope_affine (k : ℕ) (hk : k≤40) (s : ℝ)
    (ha : basisKnot k≤s) (hb : s≤basisKnot (k+1)) :
    envelope s=(1-(s-basisKnot k)/(basisKnot (k+1)-basisKnot k))*height k+
      ((s-basisKnot k)/(basisKnot (k+1)-basisKnot k))*height (k+1) := by
  interval_cases k
  · have h := envelope_segment_0 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_1 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_2 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_3 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_4 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_5 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_6 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_7 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_8 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_9 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_10 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_11 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_12 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_13 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_14 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_15 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_16 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_17 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_18 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_19 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_20 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_21 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_22 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_23 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_24 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_25 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_26 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_27 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_28 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_29 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_30 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_31 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_32 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_33 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_34 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_35 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_36 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_37 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_38 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_39 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring
  · have h := envelope_segment_40 s
      (by norm_num [basisKnot,basisLimit] at ha; exact ha)
      (by norm_num [basisKnot,basisLimit] at hb; exact hb)
    rw [h]
    norm_num [basisKnot,basisLimit,height,Certificate.knotBounds]
    <;> ring

theorem envelope_interpolation (s : ℝ) (hs : 0≤s) (hs1 : s≤basisLimit) :
    envelope s=(1-basisInterpolationParameter s)*height (basisInterval s)+
      basisInterpolationParameter s*height (basisInterval s+1) := by
  obtain ⟨ha,hb⟩ := basisInterval_brackets s hs hs1
  exact envelope_affine _ (basisInterval_le s hs hs1) s ha hb

theorem envelope_lower (s : ℝ) (hs : 0≤s) (hs1 : s≤basisLimit) : -9≤envelope s := by
  rw [envelope_interpolation s hs hs1]
  obtain ⟨ht0,ht1⟩ := basisInterpolationParameter_bounds s hs hs1
  have hk := basisInterval_le s hs hs1
  have h0 := mul_le_mul_of_nonneg_left (height_lower (basisInterval s) (by omega))
    (show 0≤1-basisInterpolationParameter s by linarith)
  have h1 := mul_le_mul_of_nonneg_left (height_lower (basisInterval s+1) (by omega)) ht0
  nlinarith

theorem envelope_zero : envelope 0=height 0 := by
  have h := envelope_segment_0 0 (by norm_num) (by norm_num)
  simpa [height,Certificate.knotBounds] using h

/-- The ONLY remaining numerical hypothesis is a bound at each of 42 knots,
for every positive contour height. External checker results are not axioms. -/
def KnotCertificate : Prop := ∀ k : ℕ,k≤41 → ∀ y : ℝ,0<y →
  certificateG y-2*Real.pi*y+
    basisKnot k*analyticBasisPotential (basisKnotWeight k) ((normalizedContourPoint y)^2)≤height k

theorem pointwise_of_knots (hknots : KnotCertificate) (s y : ℝ)
    (hs : 0≤s) (hs1 : s≤basisLimit) (hy : 0<y) :
    certificateG y-2*Real.pi*y+
      s*analyticBasisPotential (concreteBasisWeight s) ((normalizedContourPoint y)^2)≤envelope s := by
  by_cases hzero : s=0
  · subst s
    have h := hknots 0 (by omega) y hy
    simpa [basisKnot,envelope_zero] using h
  have hpos : 0<s := lt_of_le_of_ne hs (Ne.symm hzero)
  obtain ⟨ht0,ht1⟩ := basisInterpolationParameter_bounds s hs hs1
  have hk := basisInterval_le s hs hs1
  have h := interpolatedMass_upper
    (basisKnot (basisInterval s)) (basisKnot (basisInterval s+1))
    (basisInterpolationParameter s) (certificateG y-2*Real.pi*y)
    (height (basisInterval s)) (height (basisInterval s+1))
    (basisKnotWeight (basisInterval s)) (basisKnotWeight (basisInterval s+1))
    (fun l => Real.log (analyticDistance ((normalizedContourPoint y)^2) l)) ht0 ht1
    (hknots _ (by omega) y hy) (hknots _ (by omega) y hy)
  rw [envelope_interpolation s hs hs1]
  convert h using 1
  congr 1
  unfold analyticBasisPotential concreteBasisWeight
  simp only [if_neg (not_le.mpr hpos),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  field_simp

theorem numerical_rate_of_knots (hknots : KnotCertificate) :
    ∃ E : ℕ→ℝ,
      Tendsto (fun n : ℕ => E n/(n:ℝ)^2) atTop (𝓝 0) ∧
      ∀ n : ℕ,1≤n → ∀ rows cols : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1),
      ‖((analyticZetaMatrix n).submatrix rows cols).det‖≤
        Real.exp ((100*(n:ℝ))^2*(-577853339/50000000)+E n) := by
  apply analyticZetaMatrix_numerical_rate_of_certificate envelope envelope_continuous.continuousOn (-9)
    envelope_lower (pointwise_of_knots hknots)
  exact le_of_eq envelope_integral

/-- The finite-interval obligation; the infinite tail is proved below. -/
def FiniteKnotCertificate : Prop := ∀ k : ℕ,k≤41 → ∀ y : ℝ,0<y → y≤5 →
  certificateG y-2*Real.pi*y+
    basisKnot k*analyticBasisPotential (basisKnotWeight k) ((normalizedContourPoint y)^2)≤height k

theorem knotCertificate_of_finite (hfinite : FiniteKnotCertificate) : KnotCertificate := by
  intro k hk y hy
  by_cases hsmall : y≤5
  · exact hfinite k hk y hy hsmall
  · have hs1 : basisKnot k≤basisLimit := by
      interval_cases k <;> norm_num [basisKnot,basisLimit]
    exact (certificate_tail (basisKnot k) y (basisKnotWeight k) (basisKnot_nonneg k) hs1
      (le_of_lt (lt_of_not_ge hsmall)) (certificateWeight_nonneg _) (certificateWeight_sum _)).trans
      (height_lower k hk)

theorem numerical_rate_of_finite_certificate (hfinite : FiniteKnotCertificate) :
    ∃ E : ℕ→ℝ,
      Tendsto (fun n : ℕ => E n/(n:ℝ)^2) atTop (𝓝 0) ∧
      ∀ n : ℕ,1≤n → ∀ rows cols : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1),
      ‖((analyticZetaMatrix n).submatrix rows cols).det‖≤
        Real.exp ((100*(n:ℝ))^2*(-577853339/50000000)+E n) :=
  numerical_rate_of_knots (knotCertificate_of_finite hfinite)

end OddZeta.FourValue.Numerical


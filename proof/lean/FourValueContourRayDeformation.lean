import FourValueContourReparametrization

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory

theorem analyticContour_upper_finite_deformation (n : ℕ) (P : ℂ[X]) (T : ℝ) (hT : 0≤T) :
    (∫ t in (0:ℝ)..T,analyticZetaFunction n P (upperContourRay n t)*contourKernel (upperContourRay n t)*(3/5+Complex.I))=
    (∫ t in (0:ℝ)..T,analyticZetaFunction n P (verticalContourLine (100*n:ℕ) t)*contourKernel (verticalContourLine (100*n:ℕ) t)*Complex.I)+
    (∫ x in (((100*n:ℕ):ℝ)+1/2)..(((100*n:ℕ):ℝ)+1/2+(3/5)*T),horizontalContourIntegrand n P T x) := by
  let f := fun z => analyticZetaFunction n P z*contourKernel z
  let p : ℂ := (100*n:ℕ)+1/2
  let q : ℂ := p+(T:ℂ)*Complex.I
  let r : ℂ := p+(3/5:ℂ)*T+(T:ℂ)*Complex.I
  have ht := analyticContour_upper_triangle_zero n P (100*n:ℕ) T hT
  change contourSegmentIntegral f p q+contourSegmentIntegral f q r+contourSegmentIntegral f r p=0 at ht
  rw [contourSegmentIntegral_reverse f p r] at ht
  have hv := contourSegmentIntegral_affine f p Complex.I 0 T
  have hv' : contourSegmentIntegral f p q=
      ∫ t in (0:ℝ)..T,analyticZetaFunction n P (verticalContourLine (100*n:ℕ) t)*contourKernel (verticalContourLine (100*n:ℕ) t)*Complex.I := by
    simpa [f,p,q,verticalContourLine,mul_comm] using hv
  have hu := contourSegmentIntegral_affine f p (3/5+Complex.I) 0 T
  have hr : p+(T:ℂ)*(3/5+Complex.I)=r := by dsimp [r]; ring
  have hu' : contourSegmentIntegral f p r=
      ∫ t in (0:ℝ)..T,analyticZetaFunction n P (upperContourRay n t)*contourKernel (upperContourRay n t)*(3/5+Complex.I) := by
    simp only [Complex.ofReal_zero,zero_mul,add_zero,hr] at hu
    convert hu using 1
    apply intervalIntegral.integral_congr
    intro t _
    have he : p+(t:ℂ)*(3/5+Complex.I)=upperContourRay n t := by
      unfold upperContourRay baseContourRay
      dsimp [p]
      push_cast
      ring
    simp only [f,he]
  have hh := contourSegmentIntegral_affine f ((T:ℂ)*Complex.I) 1
    (((100*n:ℕ):ℝ)+1/2) (((100*n:ℕ):ℝ)+1/2+(3/5)*T)
  have hh' : contourSegmentIntegral f q r=
      ∫ x in (((100*n:ℕ):ℝ)+1/2)..(((100*n:ℕ):ℝ)+1/2+(3/5)*T),horizontalContourIntegrand n P T x := by
    convert hh using 1
    · congr 1 <;> dsimp [q,r,p] <;> push_cast <;> ring
    · apply intervalIntegral.integral_congr
      intro x _
      simp only [f,horizontalContourIntegrand,mul_one]
      congr 2 <;> push_cast <;> ring
  rw [hv',hh',hu'] at ht
  linear_combination -ht

theorem analyticContour_lower_finite_deformation (n : ℕ) (P : ℂ[X]) (T : ℝ) (hT : 0≤T) :
    (∫ t in (0:ℝ)..T,analyticZetaFunction n P (lowerContourRay n t)*contourKernel (lowerContourRay n t)*(3/5-Complex.I))=
    (∫ t in (0:ℝ)..(-T),analyticZetaFunction n P (verticalContourLine (100*n:ℕ) t)*contourKernel (verticalContourLine (100*n:ℕ) t)*Complex.I)+
    (∫ x in (((100*n:ℕ):ℝ)+1/2)..(((100*n:ℕ):ℝ)+1/2+(3/5)*T),horizontalContourIntegrand n P (-T) x) := by
  let f := fun z => analyticZetaFunction n P z*contourKernel z
  let p : ℂ := (100*n:ℕ)+1/2
  let q : ℂ := p-(T:ℂ)*Complex.I
  let r : ℂ := p+(3/5:ℂ)*T-(T:ℂ)*Complex.I
  have ht := analyticContour_lower_triangle_zero n P (100*n:ℕ) T hT
  change contourSegmentIntegral f p q+contourSegmentIntegral f q r+contourSegmentIntegral f r p=0 at ht
  rw [contourSegmentIntegral_reverse f p r] at ht
  have hv := contourSegmentIntegral_affine f p Complex.I 0 (-T)
  have hv' : contourSegmentIntegral f p q=
      ∫ t in (0:ℝ)..(-T),analyticZetaFunction n P (verticalContourLine (100*n:ℕ) t)*contourKernel (verticalContourLine (100*n:ℕ) t)*Complex.I := by
    simpa [f,p,q,verticalContourLine,mul_comm,sub_eq_add_neg] using hv
  have hu := contourSegmentIntegral_affine f p (3/5-Complex.I) 0 T
  have hr : p+(T:ℂ)*(3/5-Complex.I)=r := by dsimp [r]; ring
  have hu' : contourSegmentIntegral f p r=
      ∫ t in (0:ℝ)..T,analyticZetaFunction n P (lowerContourRay n t)*contourKernel (lowerContourRay n t)*(3/5-Complex.I) := by
    simp only [Complex.ofReal_zero,zero_mul,add_zero,hr] at hu
    convert hu using 1
    apply intervalIntegral.integral_congr
    intro t _
    have he : p+(t:ℂ)*(3/5-Complex.I)=lowerContourRay n t := by
      unfold lowerContourRay
      dsimp [p]
      push_cast
      ring
    simp only [f,he]
  have hh := contourSegmentIntegral_affine f ((-T:ℂ)*Complex.I) 1
    (((100*n:ℕ):ℝ)+1/2) (((100*n:ℕ):ℝ)+1/2+(3/5)*T)
  have hh' : contourSegmentIntegral f q r=
      ∫ x in (((100*n:ℕ):ℝ)+1/2)..(((100*n:ℕ):ℝ)+1/2+(3/5)*T),horizontalContourIntegrand n P (-T) x := by
    convert hh using 1
    · congr 1 <;> dsimp [q,r,p] <;> push_cast <;> ring
    · apply intervalIntegral.integral_congr
      intro x _
      simp only [f,horizontalContourIntegrand,mul_one]
      congr 2 <;> push_cast <;> ring
  rw [hv',hh',hu'] at ht
  linear_combination -ht

end OddZeta.FourValue

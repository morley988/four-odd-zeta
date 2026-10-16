import FourValueContourDisks
import FourValueContourTruncation

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory

theorem contourSegmentIntegral_reverse (f : ℂ→ℂ) (a b : ℂ) :
    contourSegmentIntegral f b a= -contourSegmentIntegral f a b := by
  have he : (fun t : ℝ => f (contourSegment b a t)*(a-b))=
      (fun t : ℝ => -(f (contourSegment a b (1-t))*(b-a))) := by
    funext t
    have h : contourSegment b a t=contourSegment a b (1-t) := by
      unfold contourSegment
      push_cast
      ring
    rw [h]
    ring
  unfold contourSegmentIntegral
  rw [he,intervalIntegral.integral_neg]
  have h := intervalIntegral.integral_comp_sub_left (fun t : ℝ => f (contourSegment a b t)*(b-a))
    (a:=0) (b:=1) 1
  simpa using congrArg Neg.neg h

theorem contourSegmentIntegral_affine (f : ℂ→ℂ) (z v : ℂ) (a b : ℝ) :
    contourSegmentIntegral f (z+(a:ℂ)*v) (z+(b:ℂ)*v)=
      ∫ t in a..b,f (z+(t:ℂ)*v)*v := by
  have he : (fun t : ℝ => f (contourSegment (z+(a:ℂ)*v) (z+(b:ℂ)*v) t)*
      ((z+(b:ℂ)*v)-(z+(a:ℂ)*v)))=
      (fun t : ℝ => (b-a) • (f (z+((a+(b-a)*t:ℝ):ℂ)*v)*v)) := by
    funext t
    have h : contourSegment (z+(a:ℂ)*v) (z+(b:ℂ)*v) t=z+((a+(b-a)*t:ℝ):ℂ)*v := by
      unfold contourSegment
      push_cast
      ring
    rw [h,Complex.real_smul]
    push_cast
    ring
  unfold contourSegmentIntegral
  rw [he,intervalIntegral.integral_smul]
  have h := intervalIntegral.smul_integral_comp_add_mul (fun t : ℝ => f (z+(t:ℂ)*v)*v)
    (a:=0) (b:=1) (b-a) a
  simpa using h

end OddZeta.FourValue

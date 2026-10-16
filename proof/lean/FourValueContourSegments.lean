import FourValueContourHolomorphic
import Mathlib.Analysis.Complex.HasPrimitives

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory Set Metric

def contourSegment (a b : ℂ) (t : ℝ) : ℂ := a+(t:ℂ)*(b-a)
def contourSegmentIntegral (f : ℂ→ℂ) (a b : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1,f (contourSegment a b t)*(b-a)

theorem contourSegment_mem_convex {s : Set ℂ} (hs : Convex ℝ s) {a b : ℂ}
    (ha : a∈s) (hb : b∈s) {t : ℝ} (ht : t∈Icc 0 1) : contourSegment a b t∈s := by
  simpa [contourSegment,Complex.real_smul] using hs.add_smul_mem ha (by simpa using hb) ht

theorem contourSegment_hasDerivAt (a b : ℂ) (t : ℝ) :
    HasDerivAt (contourSegment a b) (b-a) t := by
  unfold contourSegment
  convert (((hasDerivAt_id t).smul_const (b-a)).const_add a) using 1
  · rfl
  · funext x; simp [Complex.real_smul]
  · simp

theorem contourSegmentIntegral_primitive (f F : ℂ→ℂ) (s : Set ℂ) (hs : Convex ℝ s)
    (hf : ContinuousOn f s) (hF : ∀ z∈s,HasDerivAt F (f z) z)
    (a b : ℂ) (ha : a∈s) (hb : b∈s) : contourSegmentIntegral f a b=F b-F a := by
  have hm : ∀ t∈Set.uIcc (0:ℝ) 1,contourSegment a b t∈s := by
    intro t ht
    exact contourSegment_mem_convex hs ha hb (by simpa using ht)
  have hd : ∀ t∈Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t => F (contourSegment a b t)) (f (contourSegment a b t)*(b-a)) t := by
    intro t ht
    simpa only [Function.comp_def,smul_eq_mul,mul_comm] using
      (hF _ (hm t ht)).scomp t (contourSegment_hasDerivAt a b t)
  have hc : ContinuousOn (fun t => f (contourSegment a b t)*(b-a)) (Set.uIcc (0:ℝ) 1) :=
    (hf.comp (by unfold contourSegment; fun_prop) hm).mul_const _
  simpa [contourSegmentIntegral,contourSegment] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

theorem contourSegmentIntegral_triangle_ball (f : ℂ→ℂ) (c : ℂ) (R : ℝ)
    (hf : DifferentiableOn ℂ f (ball c R)) (a b d : ℂ)
    (ha : a∈ball c R) (hb : b∈ball c R) (hd : d∈ball c R) :
    contourSegmentIntegral f a b+contourSegmentIntegral f b d+contourSegmentIntegral f d a=0 := by
  obtain ⟨F,hF⟩ := hf.isExactOn_ball
  rw [contourSegmentIntegral_primitive f F _ (convex_ball c R) hf.continuousOn hF a b ha hb,
    contourSegmentIntegral_primitive f F _ (convex_ball c R) hf.continuousOn hF b d hb hd,
    contourSegmentIntegral_primitive f F _ (convex_ball c R) hf.continuousOn hF d a hd ha]
  ring

theorem analyticContourIntegrand_triangle_ball (n : ℕ) (P : ℂ[X]) (c : ℂ) (R : ℝ)
    (hball : ball c R ⊆ analyticContourDomain n) (a b d : ℂ)
    (ha : a∈ball c R) (hb : b∈ball c R) (hd : d∈ball c R) :
    contourSegmentIntegral (fun z => analyticZetaFunction n P z*contourKernel z) a b+
    contourSegmentIntegral (fun z => analyticZetaFunction n P z*contourKernel z) b d+
    contourSegmentIntegral (fun z => analyticZetaFunction n P z*contourKernel z) d a=0 :=
  contourSegmentIntegral_triangle_ball _ c R
    ((analyticContourIntegrand_differentiableOn n P).mono hball) a b d ha hb hd
end OddZeta.FourValue

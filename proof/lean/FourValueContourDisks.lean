import FourValueContourSegments

noncomputable section
namespace OddZeta.FourValue
open Polynomial Metric Set

def contourDiskCenter (a : ℤ) (H : ℝ) : ℂ := (a:ℂ)+1/2+(H:ℂ)*Complex.I
def contourDiskRadius (H : ℝ) : ℝ := Real.sqrt (H^2+1/16)

theorem integer_half_gap_sq (a k : ℤ) : (1/4:ℝ)≤((k:ℝ)-((a:ℝ)+1/2))^2 := by
  by_cases hk : k≤a
  · have : (k:ℝ)≤a := by exact_mod_cast hk
    nlinarith [sq_nonneg ((k:ℝ)-(a:ℝ))]
  · have : (a:ℝ)+1≤k := by exact_mod_cast (show a+1≤k by omega)
    nlinarith [sq_nonneg ((k:ℝ)-(a:ℝ)-1)]

theorem contourDisk_noninteger (a : ℤ) (H : ℝ) :
    ball (contourDiskCenter a H) (contourDiskRadius H) ⊆ Complex.integerComplement := by
  intro z hz
  rintro ⟨k,hk⟩
  subst z
  have hd : ‖(k:ℂ)-contourDiskCenter a H‖<contourDiskRadius H := by
    simpa [dist_eq_norm] using mem_ball.mp hz
  have hs := Real.sq_sqrt (show 0≤H^2+1/16 by positivity)
  have hn := Complex.sq_norm ((k:ℂ)-contourDiskCenter a H)
  simp [Complex.normSq_apply,contourDiskCenter] at hn
  have hg := integer_half_gap_sq a k
  have hnorm := norm_nonneg ((k:ℂ)-contourDiskCenter a H)
  have hr := Real.sqrt_nonneg (H^2+1/16)
  unfold contourDiskRadius at hd
  simp only [contourDiskCenter,one_div] at *
  nlinarith

theorem contourDisk_point_mem (a : ℤ) (H x y : ℝ)
    (h : x^2+y^2<2*H*y+1/16) :
    (a:ℂ)+1/2+(x:ℂ)+(y:ℂ)*Complex.I∈ball (contourDiskCenter a H) (contourDiskRadius H) := by
  rw [mem_ball,dist_eq_norm]
  have hn := Complex.sq_norm ((a:ℂ)+1/2+(x:ℂ)+(y:ℂ)*Complex.I-contourDiskCenter a H)
  simp [Complex.normSq_apply,contourDiskCenter] at hn
  have hs := Real.sq_sqrt (show 0≤H^2+1/16 by positivity)
  have hr := Real.sqrt_nonneg (H^2+1/16)
  unfold contourDiskRadius
  simp only [contourDiskCenter,one_div] at *
  nlinarith

theorem upperContour_triangle_vertices (a : ℤ) (T : ℝ) (hT : 0≤T) :
    let B := ball (contourDiskCenter a (T+1)) (contourDiskRadius (T+1))
    ((a:ℂ)+1/2)∈B ∧ ((a:ℂ)+1/2+(T:ℂ)*Complex.I)∈B ∧
      ((a:ℂ)+1/2+(3/5:ℂ)*T+(T:ℂ)*Complex.I)∈B := by
  dsimp only
  constructor
  · simpa using contourDisk_point_mem a (T+1) 0 0 (by norm_num)
  constructor
  · simpa using contourDisk_point_mem a (T+1) 0 T (by nlinarith [sq_nonneg T])
  · convert contourDisk_point_mem a (T+1) ((3/5)*T) T (by nlinarith [sq_nonneg T]) using 1 <;> push_cast <;> ring

theorem lowerContour_triangle_vertices (a : ℤ) (T : ℝ) (hT : 0≤T) :
    let B := ball (contourDiskCenter a (-(T+1))) (contourDiskRadius (-(T+1)))
    ((a:ℂ)+1/2)∈B ∧ ((a:ℂ)+1/2-(T:ℂ)*Complex.I)∈B ∧
      ((a:ℂ)+1/2+(3/5:ℂ)*T-(T:ℂ)*Complex.I)∈B := by
  dsimp only
  constructor
  · simpa using contourDisk_point_mem a (-(T+1)) 0 0 (by norm_num)
  constructor
  · simpa [sub_eq_add_neg] using contourDisk_point_mem a (-(T+1)) 0 (-T) (by nlinarith [sq_nonneg T])
  · convert contourDisk_point_mem a (-(T+1)) ((3/5)*T) (-T) (by nlinarith [sq_nonneg T]) using 1 <;> push_cast <;> ring

theorem analyticContour_upper_triangle_zero (n : ℕ) (P : ℂ[X]) (a : ℤ) (T : ℝ) (hT : 0≤T) :
    let f := fun z => analyticZetaFunction n P z*contourKernel z
    let p : ℂ := (a:ℂ)+1/2
    let q : ℂ := p+(T:ℂ)*Complex.I
    let r : ℂ := p+(3/5:ℂ)*T+(T:ℂ)*Complex.I
    contourSegmentIntegral f p q+contourSegmentIntegral f q r+contourSegmentIntegral f r p=0 := by
  obtain ⟨hp,hq,hr⟩ := upperContour_triangle_vertices a T hT
  exact contourSegmentIntegral_triangle_ball _ (contourDiskCenter a (T+1)) (contourDiskRadius (T+1))
    ((analyticContourIntegrand_noninteger_differentiableOn n P).mono (contourDisk_noninteger a (T+1)))
    _ _ _ hp hq hr

theorem analyticContour_lower_triangle_zero (n : ℕ) (P : ℂ[X]) (a : ℤ) (T : ℝ) (hT : 0≤T) :
    let f := fun z => analyticZetaFunction n P z*contourKernel z
    let p : ℂ := (a:ℂ)+1/2
    let q : ℂ := p-(T:ℂ)*Complex.I
    let r : ℂ := p+(3/5:ℂ)*T-(T:ℂ)*Complex.I
    contourSegmentIntegral f p q+contourSegmentIntegral f q r+contourSegmentIntegral f r p=0 := by
  obtain ⟨hp,hq,hr⟩ := lowerContour_triangle_vertices a T hT
  exact contourSegmentIntegral_triangle_ball _ (contourDiskCenter a (-(T+1))) (contourDiskRadius (-(T+1)))
    ((analyticContourIntegrand_noninteger_differentiableOn n P).mono (contourDisk_noninteger a (-(T+1))))
    _ _ _ hp hq hr
end OddZeta.FourValue

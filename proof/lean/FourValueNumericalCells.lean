import FourValueCertificatePotential
import FourValueGeometry

noncomputable section
namespace OddZeta.FourValue.Numerical

theorem contour_square_interpolation_error (l h t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    ‖(normalizedContourPoint ((1-t)*l+t*h))^2-
      (((1-t:ℝ):ℂ)*(normalizedContourPoint l)^2+(t:ℂ)*(normalizedContourPoint h)^2)‖≤
      (34/25:ℝ)*(h-l)^2/4 := by
  let c : ℂ := (3/5:ℂ)+Complex.I
  have he (x : ℝ) : c^2*(x:ℂ)^2+(2*c)*(x:ℂ)+1=(normalizedContourPoint x)^2 := by
    simp only [normalizedContourPoint,c]
    push_cast
    ring
  have hn : ‖c^2‖=(34/25:ℝ) := by
    rw [norm_pow]
    have h := Complex.sq_norm c
    rw [h]
    norm_num [c,Complex.normSq_apply]
  have hb := Geometry.quadratic_interpolation_error (c^2) (2*c) 1 l h t ht ht1
  simpa only [he,hn] using hb

theorem cutoff_cell_bound (l h t : ℝ) (ht : 0≤t) (ht1 : t≤1)
    (center : ℂ) (U : ℝ)
    (hleft : ‖(normalizedContourPoint l)^2-center‖≤U)
    (hright : ‖(normalizedContourPoint h)^2-center‖≤U) (hδ : (1/50:ℝ)≤U) :
    max ‖(normalizedContourPoint ((1-t)*l+t*h))^2-center‖ (1/50)≤
      U+(34/25:ℝ)*(h-l)^2/4 := by
  have hbd := Geometry.distance_enclosure
    ((normalizedContourPoint ((1-t)*l+t*h))^2)
    ((normalizedContourPoint l)^2) ((normalizedContourPoint h)^2) center t
    ((34/25:ℝ)*(h-l)^2/4) ht ht1 (contour_square_interpolation_error l h t ht ht1)
  apply max_le
  · exact hbd.trans (add_le_add (max_le hleft hright) le_rfl)
  · nlinarith [sq_nonneg (h-l)]

theorem basis_log_cell_bound (l h t : ℝ) (ht : 0≤t) (ht1 : t≤1)
    (j : Fin 45) (U V : ℝ)
    (hU0 : ‖(normalizedContourPoint l)^2-analyticCenter j‖≤U)
    (hU1 : ‖(normalizedContourPoint h)^2-analyticCenter j‖≤U)
    (hV0 : ‖(normalizedContourPoint l)^2-star (analyticCenter j)‖≤V)
    (hV1 : ‖(normalizedContourPoint h)^2-star (analyticCenter j)‖≤V)
    (hUδ : (1/50:ℝ)≤U) (hVδ : (1/50:ℝ)≤V) :
    Real.log (analyticDistance ((normalizedContourPoint ((1-t)*l+t*h))^2) j)≤
      Real.log (U+(34/25:ℝ)*(h-l)^2/4)+Real.log (V+(34/25:ℝ)*(h-l)^2/4) := by
  have hU := cutoff_cell_bound l h t ht ht1 (analyticCenter j) U hU0 hU1 hUδ
  have hV := cutoff_cell_bound l h t ht ht1 (star (analyticCenter j)) V hV0 hV1 hVδ
  have hUp : 0<U+(34/25:ℝ)*(h-l)^2/4 := by nlinarith [sq_nonneg (h-l)]
  have hVp : 0<V+(34/25:ℝ)*(h-l)^2/4 := by nlinarith [sq_nonneg (h-l)]
  have hp : analyticDistance ((normalizedContourPoint ((1-t)*l+t*h))^2) j≤
      (U+(34/25:ℝ)*(h-l)^2/4)*(V+(34/25:ℝ)*(h-l)^2/4) := by
    exact mul_le_mul hU hV (by positivity) hUp.le
  have he := Real.log_le_log (analyticDistance_pos _ _) hp
  rwa [Real.log_mul hUp.ne' hVp.ne'] at he

end OddZeta.FourValue.Numerical

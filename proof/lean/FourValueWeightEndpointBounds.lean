import FourValueWeightScaledBound
import FourValueActualBasisUniform

noncomputable section
namespace OddZeta.FourValue
open Polynomial

def weightEndpointConstant : ℝ := targetNormalizationLogCorrection+5/6+
  2*Real.log 2+5*Real.log 3-15*Real.log (33/100)

theorem shiftedContour_re (y ε : ℝ) :
    (normalizedContourPoint y+(ε:ℂ)).re=1+(3/5)*y+ε := by
  simp [normalizedContourPoint]

theorem shiftedContour_log_norm (y ε : ℝ) (hy : 0≤y) (hε : 0≤ε) (hε1 : ε≤1) :
    Real.log ‖normalizedContourPoint y+(ε:ℂ)‖≤Real.log 2+Real.log (1+y) := by
  have hz : 0<‖normalizedContourPoint y+(ε:ℂ)‖ := by
    have h := Complex.re_le_norm (normalizedContourPoint y+(ε:ℂ))
    rw [shiftedContour_re] at h
    linarith
  have h := Real.log_le_log hz (normalizedContourPoint_shift_norm y ε hy hε hε1)
  rwa [Real.log_mul (by norm_num) (by positivity)] at h

theorem shiftedContour_root_minus_one (y ε : ℝ) (hy : 0≤y) (hε : 0≤ε) (hε1 : ε≤1) :
    rootLogProfile (normalizedContourPoint y+(ε:ℂ)) (-1)≤Real.log 3+Real.log (1+y) := by
  have hz : (-1:ℝ)<(normalizedContourPoint y+(ε:ℂ)).re := by rw [shiftedContour_re]; linarith
  have hb : ‖normalizedContourPoint y+(ε:ℂ)-((-1:ℝ):ℂ)‖≤3*(1+y) := by
    have h := norm_sub_le (normalizedContourPoint y+(ε:ℂ)) ((-1:ℝ):ℂ)
    norm_num at h ⊢
    linarith [normalizedContourPoint_shift_norm y ε hy hε hε1]
  have h := Real.log_le_log (rootLogProfile_norm_pos _ _ hz) hb
  rwa [Real.log_mul (by norm_num) (by positivity)] at h

theorem shiftedContour_root_alpha_lower (y ε : ℝ) (hy : 0≤y) (hε : 0≤ε) (i : Fin 15) :
    Real.log (33/100)≤rootLogProfile (normalizedContourPoint y+(ε:ℂ)) (targetAlpha i) := by
  apply Real.log_le_log (by norm_num)
  have h := Complex.re_le_norm (normalizedContourPoint y+(ε:ℂ)-(targetAlpha i:ℂ))
  simp only [Complex.sub_re,Complex.ofReal_re,shiftedContour_re] at h
  linarith [(targetAlpha_bounds i).2]

theorem analyticWeight_shifted_endpoint_bound (n : ℕ) (hn : 1≤n) (y ε : ℝ)
    (hy : 0≤y) (hε : 0<ε) (hε1 : ε≤1) :
    Real.log ‖analyticZetaFunction n 1 ((100*(n:ℂ))*(normalizedContourPoint y+(ε:ℂ)))‖≤
      (100*(n:ℝ))*targetWeightPotential (normalizedContourPoint y+(ε:ℂ))-
      9*Real.log (100*(n:ℝ))+weightEndpointConstant+6*Real.log (1+y) := by
  have hw := analyticWeight_scaled_log_bound n hn (normalizedContourPoint y+(ε:ℂ))
    (by rw [shiftedContour_re]; linarith)
  have hsum := Finset.sum_le_sum (s:=Finset.univ)
    (fun (i : Fin 15) _ => shiftedContour_root_alpha_lower y ε hy hε.le i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  norm_num only [Nat.cast_ofNat] at hsum
  unfold weightEndpointConstant
  linarith [shiftedContour_log_norm y ε hy hε.le hε1,shiftedContour_root_minus_one y ε hy hε.le hε1]
end OddZeta.FourValue

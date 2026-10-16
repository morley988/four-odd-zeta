import FourValueUniformContourShift

noncomputable section
namespace OddZeta.FourValue
open Polynomial

def normalizedContourPoint (y : ℝ) : ℂ := 1+((3/5:ℝ):ℂ)*y+Complex.I*y

theorem normalizedContourPoint_norm (y : ℝ) (hy : 0≤y) :
    ‖normalizedContourPoint y‖≤1+2*y := by
  have hs : ‖((3/5:ℝ):ℂ)+Complex.I‖≤2 := by
    have h := norm_add_le (((3/5:ℝ):ℂ)) Complex.I
    norm_num at h ⊢
    linarith
  have he : normalizedContourPoint y=1+(((3/5:ℝ):ℂ)+Complex.I)*(y:ℂ) := by
    unfold normalizedContourPoint
    ring
  rw [he]
  calc
    _ ≤ ‖(1:ℂ)‖+‖(((3/5:ℝ):ℂ)+Complex.I)*(y:ℂ)‖ := norm_add_le _ _
    _ ≤ 1+2*y := by rw [norm_mul]; simpa [abs_of_nonneg hy] using add_le_add_left (mul_le_mul_of_nonneg_right hs hy) 1

theorem normalizedContourPoint_shift_norm (y ε : ℝ) (hy : 0≤y) (hε : 0≤ε) (hε1 : ε≤1) :
    ‖normalizedContourPoint y+(ε:ℂ)‖≤2*(1+y) := by
  have h := norm_add_le (normalizedContourPoint y) (ε:ℂ)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hε] at h
  linarith [normalizedContourPoint_norm y hy]

theorem shifted_contour_log_growth (y ε : ℝ) (hy : 0≤y) (hε : 0≤ε) (hε1 : ε≤1) :
    Real.log (1+‖(normalizedContourPoint y+(ε:ℂ))^2‖)≤Real.log 5+2*Real.log (1+y) := by
  have h := normalizedContourPoint_shift_norm y ε hy hε hε1
  have hn := norm_nonneg (normalizedContourPoint y+(ε:ℂ))
  have he : 1+‖(normalizedContourPoint y+(ε:ℂ))^2‖≤5*(1+y)^2 := by
    rw [norm_pow]
    nlinarith [sq_nonneg y]
  have hl := Real.log_le_log (show 0<1+‖(normalizedContourPoint y+(ε:ℂ))^2‖ by positivity) he
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hl
  simpa using hl

theorem shifted_scaled_basis_log_bound (M : ℝ) (hM : 1≤M) (i : ℕ) (hi : (i:ℝ)≤2*M)
    (w : Fin 45→ℝ) (hw : ∀ l,0≤w l) (hs : ∑ l,w l=1)
    (y : ℝ) (hy : 0≤y)
    (hz : (scaledAnalyticBasis M i w).eval ((M:ℂ)^2*(normalizedContourPoint y+(1/(2*M):ℝ))^2)≠0) :
    2*Real.log ‖(scaledAnalyticBasis M i w).eval ((M:ℂ)^2*(normalizedContourPoint y+(1/(2*M):ℝ))^2)‖≤
      4*(i:ℝ)*Real.log M-2*Real.log (Nat.factorial (2*i):ℝ)+
      (i:ℝ)*analyticBasisPotential w ((normalizedContourPoint y)^2)+
      90*Real.log 4+90*Real.log 2500+180*Real.log 5+360*Real.log (1+y)+500 := by
  have hM0 : 0<M := by linarith
  have he0 : (0:ℝ)≤1/(2*M) := by positivity
  have he1 : (1:ℝ)/(2*M)≤1 := (div_le_one (by positivity)).mpr (by linarith)
  have hb := scaledAnalyticBasis_log_bound M hM0 i w hw hs
    ((normalizedContourPoint y+(1/(2*M):ℝ))^2) hz
  have hp := mul_le_mul_of_nonneg_left
    (analyticBasisPotential_squared_shift w hw hs (normalizedContourPoint y) (1/(2*M)) he0 he1)
    (Nat.cast_nonneg (α:=ℝ) i)
  have hg := shifted_contour_log_growth y (1/(2*M)) hy he0 he1
  have hc : (i:ℝ)*(500*(1/(2*M)))≤500 := by
    have h := mul_le_mul_of_nonneg_right hi (show 0≤500*(1/(2*M)) by positivity)
    have he : 2*M*(500*(1/(2*M)))=500 := by field_simp
    rwa [he] at h
  nlinarith
end OddZeta.FourValue

import FourValueActualAdaptedBasis
import FourValueRootCoefficientBounds

noncomputable section
namespace OddZeta.FourValue
open Polynomial

def actualAdaptedMonic (n i : ℕ) : ℂ[X] := C (Nat.factorial (2*i):ℂ)*actualAdaptedBasis n i

theorem actualAdaptedMonic_monic (n i : ℕ) (hn : 1≤n) (hi : i≤targetHankelDegree n) :
    (actualAdaptedMonic n i).Monic :=
  scaledAnalyticBasis_factorial_monic _ (by exact_mod_cast (show 100*n≠0 by omega)) i _
    (adaptedWeights_nonneg n i hn hi) (adaptedWeights_sum n i hn hi)

theorem actualAdaptedMonic_natDegree (n i : ℕ) (hn : 1≤n) (hi : i≤targetHankelDegree n) :
    (actualAdaptedMonic n i).natDegree=i := by
  rw [actualAdaptedMonic,natDegree_C_mul (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
    actualAdaptedBasis_natDegree n i hn hi]

theorem actualAdaptedMonic_root_bound (n i : ℕ) (hn : 1≤n) (z : ℂ)
    (hz : (actualAdaptedMonic n i).eval z=0) : ‖z‖≤3*((100*n:ℕ):ℝ)^2 := by
  let M : ℝ := (100*n:ℕ)
  have hM : 0<M := by dsimp [M]; exact_mod_cast (show 0<100*n by omega)
  have hMc : (M:ℂ)≠0 := by exact_mod_cast hM.ne'
  have hf : (Nat.factorial (2*i):ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hq : (scaledAnalyticBasis M i (adaptedWeights n i)).eval z=0 := by
    simpa [actualAdaptedMonic,actualAdaptedBasis,eval_mul,eval_C,hf,M] using hz
  have he : (M:ℂ)^2*(z/(M:ℂ)^2)=z := by field_simp
  rw [← he,scaledAnalyticBasis_eval M hM.ne'] at hq
  have hp : (concreteAnalyticBasis i (adaptedWeights n i)).eval (z/(M:ℂ)^2)=0 :=
    (mul_eq_zero.mp hq).resolve_left (div_ne_zero (pow_ne_zero _ hMc) hf)
  have hb := concreteAnalyticBasis_root_bound i (adaptedWeights n i) (z/(M:ℂ)^2) hp
  have hb' : ‖z‖/M^2≤3 := by
    have hb3 : ‖z/(M:ℂ)^2‖≤3 := hb.trans (by norm_num)
    simpa [norm_div,norm_pow,abs_of_pos hM] using hb3
  exact (div_le_iff₀ (sq_pos_of_pos hM)).mp hb'

theorem squareRootProduct_root_bound (i m : ℕ) (hi : i≤m) (z : ℂ)
    (hz : (squareRootProduct (K:=ℂ) i).eval z=0) : ‖z‖≤(m:ℝ)^2 := by
  rw [squareRootProduct,linearRootProduct_eval_zero_iff] at hz
  obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hz
  have hh' : h<m := (List.mem_range.mp hh).trans_le hi
  simp only [norm_pow,Complex.norm_natCast]
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hh'.le) 2

def analyticRootRadius (n : ℕ) : ℝ := 4*((100*n:ℕ):ℝ)^2

theorem analyticRootRadius_pos (n : ℕ) (hn : 1≤n) : 0<analyticRootRadius n := by
  have : (0:ℝ)<(100*n:ℕ) := by exact_mod_cast (show 0<100*n by omega)
  unfold analyticRootRadius
  positivity

theorem actualAdaptedMonic_common_root_bound (n i : ℕ) (hn : 1≤n) (z : ℂ)
    (hz : (actualAdaptedMonic n i).eval z=0) : ‖z‖≤analyticRootRadius n := by
  have h := actualAdaptedMonic_root_bound n i hn z hz
  unfold analyticRootRadius
  nlinarith [sq_nonneg (((100*n:ℕ):ℝ))]

theorem squareRootProduct_common_root_bound (n i : ℕ) (hi : i≤targetHankelDegree n) (z : ℂ)
    (hz : (squareRootProduct (K:=ℂ) i).eval z=0) : ‖z‖≤analyticRootRadius n := by
  have h := squareRootProduct_root_bound i (200*n) (by unfold targetHankelDegree at hi; omega) z hz
  unfold analyticRootRadius
  push_cast at h ⊢
  nlinarith
end OddZeta.FourValue

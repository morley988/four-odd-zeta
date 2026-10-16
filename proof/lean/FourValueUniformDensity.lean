import FourValueWeightUniform
import FourValueFactorialRowError

noncomputable section
namespace OddZeta.FourValue
open Polynomial

def basisUniformConstant : ℝ := 90*Real.log 4+90*Real.log 2500+180*Real.log 5+500

def contourRate (s y : ℝ) : ℝ := targetWeightPotential (normalizedContourPoint y)-2*Real.pi*y+
  s*analyticBasisPotential (concreteBasisWeight s) ((normalizedContourPoint y)^2)

def contourDensity (n i : ℕ) (t : ℝ) : ℝ :=
  ‖(actualAdaptedBasis n i).eval ((upperContourRay n t)^2)‖^2*
    ‖analyticContourWeight n (upperContourRay n t)‖

theorem norm_le_exp_of_log_bound (z : ℂ) (b : ℝ) (h : Real.log ‖z‖≤b) : ‖z‖≤Real.exp b := by
  by_cases hz : z=0
  · simp [hz,(Real.exp_pos b).le]
  · exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr hz)).mp h

theorem actual_basis_weight_log_bound (n i : ℕ) (hn : 1≤n) (hi : i≤targetHankelDegree n)
    (y : ℝ) (hy : 0<y)
    (hq : (actualAdaptedBasis n i).eval ((upperContourRay n (100*(n:ℝ)*y))^2)≠0) :
    2*Real.log ‖(actualAdaptedBasis n i).eval ((upperContourRay n (100*(n:ℝ)*y))^2)‖+
      Real.log ‖analyticZetaFunction n 1 (upperContourRay n (100*(n:ℝ)*y))‖≤
      (100*(n:ℝ))*(contourRate (adaptedIndexMass n i) y+2*Real.pi*y+
        factorialRowRate (adaptedIndexMass n i))+
      basisUniformConstant+weightUniformConstant+369*Real.log (1+y) := by
  have hM : (1:ℝ)≤100*(n:ℝ) := by exact_mod_cast (show 1≤100*n by omega)
  have hM0 : (0:ℝ)<100*(n:ℝ) := by linarith
  have hb := actualAdaptedBasis_uniform_log_bound n i hn hi y hy.le hq
  have hw := analyticWeight_uniform_log_bound n hn y hy
  have hf := factorial_row_main_upper i (100*(n:ℝ)) hM0
  have hlogM := Real.log_nonneg hM
  have hlogy := Real.log_nonneg (show (1:ℝ)≤1+y by linarith)
  have hindex : (100*(n:ℝ))*adaptedIndexMass n i=(i:ℝ) := by
    unfold adaptedIndexMass
    push_cast
    field_simp
  unfold contourRate basisUniformConstant
  change _≤100*(n:ℝ)*(targetWeightPotential (normalizedContourPoint y)-2*Real.pi*y+
    adaptedIndexMass n i*analyticBasisPotential (adaptedWeights n i) ((normalizedContourPoint y)^2)+
    2*Real.pi*y+factorialRowRate (adaptedIndexMass n i))+_+_+_
  have hf' : 4*(i:ℝ)*Real.log (100*(n:ℝ))-2*Real.log (Nat.factorial (2*i):ℝ)≤
      (100*(n:ℝ))*factorialRowRate (adaptedIndexMass n i) := by simpa [adaptedIndexMass] using hf
  nlinarith [congrArg (fun x : ℝ => x*analyticBasisPotential (adaptedWeights n i) ((normalizedContourPoint y)^2)) hindex]

theorem contourDensity_uniform_bound : ∃ C : ℝ,0<C ∧ ∀ n i : ℕ,1≤n → i≤targetHankelDegree n →
    ∀ y : ℝ,0<y → contourDensity n i (100*(n:ℝ)*y)≤
      C*(1+y)^369*Real.exp ((100*(n:ℝ))*(contourRate (adaptedIndexMass n i) y+
        factorialRowRate (adaptedIndexMass n i))) := by
  obtain ⟨K,hK,hkernel⟩ := contourKernel_upperRay_bound
  let C : ℝ := (K+1)*Real.exp (basisUniformConstant+weightUniformConstant)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro n i hn hi y hy
  let z := upperContourRay n (100*(n:ℝ)*y)
  let q := (actualAdaptedBasis n i).eval (z^2)
  let w := analyticZetaFunction n 1 z
  have hM0 : (0:ℝ)<100*(n:ℝ) := by exact_mod_cast (show 0<100*n by omega)
  have hk := hkernel n (100*(n:ℝ)*y) (by positivity)
  change ‖contourKernel z‖≤K*Real.exp (-2*Real.pi*(100*(n:ℝ)*y)) at hk
  change ‖q‖^2*‖w*contourKernel z‖≤_
  rw [norm_mul]
  by_cases hq : q=0
  · rw [hq,norm_zero,zero_pow (by decide),zero_mul]
    positivity
  by_cases hw : w=0
  · rw [hw,norm_zero,zero_mul,mul_zero]
    positivity
  have hb := actual_basis_weight_log_bound n i hn hi y hy hq
  change 2*Real.log ‖q‖+Real.log ‖w‖≤_ at hb
  have hqw : ‖q‖^2*‖w‖≤Real.exp ((100*(n:ℝ))*(contourRate (adaptedIndexMass n i) y+
      2*Real.pi*y+factorialRowRate (adaptedIndexMass n i))+
      basisUniformConstant+weightUniformConstant+369*Real.log (1+y)) := by
    apply (Real.log_le_iff_le_exp (by positivity)).mp
    rwa [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hq)) (norm_ne_zero_iff.mpr hw),Real.log_pow]
  calc
    _ = (‖q‖^2*‖w‖)*‖contourKernel z‖ := by ring
    _ ≤ Real.exp ((100*(n:ℝ))*(contourRate (adaptedIndexMass n i) y+2*Real.pi*y+
          factorialRowRate (adaptedIndexMass n i))+basisUniformConstant+weightUniformConstant+
          369*Real.log (1+y))*(K*Real.exp (-2*Real.pi*(100*(n:ℝ)*y))) :=
      mul_le_mul hqw hk (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp ((100*(n:ℝ))*(contourRate (adaptedIndexMass n i) y+2*Real.pi*y+
          factorialRowRate (adaptedIndexMass n i))+basisUniformConstant+weightUniformConstant+
          369*Real.log (1+y))*((K+1)*Real.exp (-2*Real.pi*(100*(n:ℝ)*y))) := by gcongr; linarith
    _ = _ := by
      dsimp [C]
      have hy0 : 0<1+y := by linarith
      have hp : (1+y)^369=Real.exp (369*Real.log (1+y)) := by simpa only [Real.exp_log hy0,Nat.cast_ofNat] using (Real.exp_nat_mul (Real.log (1+y)) 369).symm
      rw [hp]
      calc
        _ = (K+1)*Real.exp (((100*(n:ℝ))*(contourRate (adaptedIndexMass n i) y+2*Real.pi*y+
          factorialRowRate (adaptedIndexMass n i))+basisUniformConstant+weightUniformConstant+
          369*Real.log (1+y))+(-2*Real.pi*(100*(n:ℝ)*y))) := by rw [Real.exp_add (x:=((100*(n:ℝ))*(contourRate (adaptedIndexMass n i) y+2*Real.pi*y+factorialRowRate (adaptedIndexMass n i))+basisUniformConstant+weightUniformConstant+369*Real.log (1+y)))]; ring
        _ = (K+1)*Real.exp ((basisUniformConstant+weightUniformConstant)+369*Real.log (1+y)+
          (100*(n:ℝ))*(contourRate (adaptedIndexMass n i) y+factorialRowRate (adaptedIndexMass n i))) := by congr 2; ring
        _ = _ := by rw [Real.exp_add,Real.exp_add]; ring
end OddZeta.FourValue

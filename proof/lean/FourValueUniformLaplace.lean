import FourValueRateMajorant
import FourValueLaplaceMajorant

noncomputable section
namespace OddZeta.FourValue
open MeasureTheory Set

theorem uniform_laplace_pointwise (M F V R A L y : ℝ) (hM : 1≤M) (hV : L≤V)
    (hF : F≤V) (hmajor : F≤A+18*Real.log (1+y)-2*Real.pi*y) (hy : 0<y) :
    (1+y)^369*Real.exp (M*(F+R))≤
      Real.exp (M*(V+R))*Real.exp (A-L)*((1+y)^387*Real.exp (-2*Real.pi*y)) := by
  have he : M*(F+R)≤M*(V+R)+(A-L)+18*Real.log (1+y)-2*Real.pi*y := by
    nlinarith [mul_nonneg (show 0≤M-1 by linarith) (sub_nonneg.mpr hF)]
  have hb := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (show 0≤(1+y)^369 by positivity)
  refine hb.trans_eq ?_
  have hlog : Real.exp (18*Real.log (1+y))=(1+y)^18 := by
    simpa only [Nat.cast_ofNat,Real.exp_log (show 0<1+y by linarith)] using Real.exp_nat_mul (Real.log (1+y)) 18
  rw [show M*(V+R)+(A-L)+18*Real.log (1+y)-2*Real.pi*y=
    (M*(V+R)+(A-L))+(18*Real.log (1+y)+(-2*Real.pi*y)) by ring,
    Real.exp_add,Real.exp_add,Real.exp_add,hlog]
  have hp : (1+y)^369*(1+y)^18=(1+y)^387 := by rw [← pow_add]
  calc
    _ = Real.exp (M*(V+R))*Real.exp (A-L)*
        (((1+y)^369*(1+y)^18)*Real.exp (-2*Real.pi*y)) := by ac_rfl
    _ = _ := by rw [hp]

theorem contourDensity_integrable (n i : ℕ) (hn : 1≤n) (hi : i≤targetHankelDegree n) :
    IntegrableOn (contourDensity n i) (Ioi 0) :=
  contourRayEnergy_integrable n _ _ (analyticZetaFunction_upperContour_integrable n _
    (actualAdaptedBasis_product_degree n i i hn hi hi))

theorem contourEnergy_scaled_integral (n i : ℕ) (hn : 1≤n) :
    contourRayEnergy n (actualAdaptedBasis n i) (upperContourRay n)=
      (100*(n:ℝ))*(∫ y in Ioi (0:ℝ),contourDensity n i (100*(n:ℝ)*y)) := by
  have hM : (0:ℝ)<100*(n:ℝ) := by exact_mod_cast (show 0<100*n by omega)
  have h := integral_comp_mul_left_Ioi' (contourDensity n i) 0 hM
  simpa only [mul_zero,smul_eq_mul,contourRayEnergy,contourDensity] using h.symm

theorem actualContourEnergy_uniform_laplace (L : ℝ) : ∃ C : ℝ,0<C ∧
    ∀ n i : ℕ,1≤n → i≤targetHankelDegree n → ∀ V : ℝ,L≤V →
      (∀ y : ℝ,0<y → contourRate (adaptedIndexMass n i) y≤V) →
      contourRayEnergy n (actualAdaptedBasis n i) (upperContourRay n)≤
        (100*(n:ℝ))*C*Real.exp ((100*(n:ℝ))*(V+factorialRowRate (adaptedIndexMass n i))) := by
  obtain ⟨B,hB,hbound⟩ := contourDensity_uniform_bound
  let g : ℝ→ℝ := fun y => (1+y)^387*Real.exp (-2*Real.pi*y)
  have hg : IntegrableOn g (Ioi 0) := by
    simpa only [g,neg_mul] using polynomial_exp_integrable 387 (2*Real.pi) (by positivity)
  let J : ℝ := ∫ y in Ioi (0:ℝ),g y
  have hJ : 0≤J := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro y hy
    have hy0 : 0<y := hy
    dsimp [g]
    positivity
  let C : ℝ := B*Real.exp (contourRateMajorantConstant-L)*(J+1)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro n i hn hi V hV hcert
  let M : ℝ := 100*(n:ℝ)
  let R := factorialRowRate (adaptedIndexMass n i)
  have hM : 1≤M := by dsimp [M]; exact_mod_cast (show 1≤100*n by omega)
  have hM0 : 0<M := by linarith
  have hs := adaptedIndexMass_bounds n i hn hi
  have hd : IntegrableOn (fun y => contourDensity n i (M*y)) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff (contourDensity n i) 0 hM0).mpr
      (by simpa using contourDensity_integrable n i hn hi)
    exact h
  have hpoint (y : ℝ) (hy : 0<y) : contourDensity n i (M*y)≤
      (B*Real.exp (M*(V+R))*Real.exp (contourRateMajorantConstant-L))*g y := by
    have h1 := hbound n i hn hi y hy
    have h2 := uniform_laplace_pointwise M (contourRate (adaptedIndexMass n i) y) V R
      contourRateMajorantConstant L y hM hV (hcert y hy)
      (contourRate_coarse_bound _ _ hs.1 hs.2 hy) hy
    have h3 := mul_le_mul_of_nonneg_left h2 hB.le
    change _≤B*(Real.exp (M*(V+R))*Real.exp (contourRateMajorantConstant-L)*g y) at h3
    calc
      _ ≤ B*((1+y)^369*Real.exp (M*(contourRate (adaptedIndexMass n i) y+R))) := by simpa [M,R,mul_assoc] using h1
      _ ≤ _ := by simpa only [mul_assoc] using h3
  have hint := setIntegral_mono_on hd (hg.const_mul (B*Real.exp (M*(V+R))*Real.exp (contourRateMajorantConstant-L)))
    measurableSet_Ioi hpoint
  rw [integral_const_mul] at hint
  change _≤(B*Real.exp (M*(V+R))*Real.exp (contourRateMajorantConstant-L))*J at hint
  rw [contourEnergy_scaled_integral n i hn]
  have h := mul_le_mul_of_nonneg_left hint hM0.le
  dsimp [C]
  change M*(∫ y in Ioi (0:ℝ),contourDensity n i (M*y))≤
    M*(B*Real.exp (contourRateMajorantConstant-L)*(J+1))*Real.exp (M*(V+R))
  calc
    _ ≤ M*((B*Real.exp (M*(V+R))*Real.exp (contourRateMajorantConstant-L))*J) := h
    _ ≤ M*((B*Real.exp (M*(V+R))*Real.exp (contourRateMajorantConstant-L))*(J+1)) := by gcongr; linarith
    _ = _ := by ring
end OddZeta.FourValue

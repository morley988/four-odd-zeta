import FourValueContourResidues
import FourValueContourEnergy

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory Set

theorem contourKernel_differentiableOn : DifferentiableOn ℂ contourKernel Complex.integerComplement := by
  have hd : ContDiffOn ℂ 5 (fun z : ℂ => (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*z))
      Complex.integerComplement := by
    unfold Complex.cot
    apply ContDiffOn.mul contDiffOn_const
    exact ContDiffOn.div (by fun_prop) (by fun_prop) (fun z hz => sin_pi_mul_ne_zero hz)
  have h := hd.differentiableOn_iteratedDerivWithin (m:=4) (by norm_num)
    Complex.isOpen_compl_range_intCast.uniqueDiffOn
  have h' : DifferentiableOn ℂ (iteratedDeriv 4
      (fun z : ℂ => (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*z))) Complex.integerComplement := by
    apply h.congr
    intro z hz
    exact (iteratedDerivWithin_of_isOpen Complex.isOpen_compl_range_intCast hz).symm
  exact h'.div_const 24

theorem analyticZetaDenominator_regular_noninteger (n : ℕ) (z : ℂ)
    (hz : z∈Complex.integerComplement) :
    (tupleDenominator (K:=ℂ) (targetEndpointTuple n)).eval z≠0 := by
  simp only [tupleDenominator,eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ he
  obtain ⟨j,_,_,hj⟩ := (centeredDenominator_eval_zero_iff (targetEndpointTuple n i) z).mp he
  exact hz ⟨j,hj.symm⟩

theorem analyticContourIntegrand_noninteger_differentiableOn (n : ℕ) (P : ℂ[X]) :
    DifferentiableOn ℂ (fun z => analyticZetaFunction n P z*contourKernel z) Complex.integerComplement := by
  have hR : DifferentiableOn ℂ (analyticZetaFunction n P) Complex.integerComplement := by
    unfold analyticZetaFunction targetZetaFunction
    exact (Polynomial.differentiable _).differentiableOn.div (Polynomial.differentiable _).differentiableOn
      (fun z hz => analyticZetaDenominator_regular_noninteger n z hz)
  exact hR.mul contourKernel_differentiableOn

def analyticContourDomain (n : ℕ) : Set ℂ :=
  {z | ((67*n:ℕ):ℝ)<z.re} ∩ Complex.integerComplement

theorem analyticContourDomain_isOpen (n : ℕ) : IsOpen (analyticContourDomain n) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter Complex.isOpen_compl_range_intCast

theorem analyticContourIntegrand_differentiableOn (n : ℕ) (P : ℂ[X]) :
    DifferentiableOn ℂ (fun z => analyticZetaFunction n P z*contourKernel z) (analyticContourDomain n) :=
  ((analyticZetaFunction_differentiableOn n P).mono inter_subset_left).mul
    (contourKernel_differentiableOn.mono inter_subset_right)

theorem analyticContourIntegrand_rectangle_zero (n : ℕ) (P : ℂ[X]) (z w : ℂ)
    (hrect : Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im ⊆ analyticContourDomain n) :
    (∫ x : ℝ in z.re..w.re, analyticZetaFunction n P (x+z.im*Complex.I)*contourKernel (x+z.im*Complex.I))-
    (∫ x : ℝ in z.re..w.re, analyticZetaFunction n P (x+w.im*Complex.I)*contourKernel (x+w.im*Complex.I))+
    Complex.I*(∫ y : ℝ in z.im..w.im, analyticZetaFunction n P (w.re+y*Complex.I)*contourKernel (w.re+y*Complex.I))-
    Complex.I*(∫ y : ℝ in z.im..w.im, analyticZetaFunction n P (z.re+y*Complex.I)*contourKernel (z.re+y*Complex.I))=0 := by
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn _ z w
    ((analyticContourIntegrand_differentiableOn n P).mono hrect)

theorem upperRectangle_subset_analyticContourDomain (n : ℕ) (a b c d : ℝ)
    (hab : a≤b) (hcd : c≤d) (ha : ((67*n:ℕ):ℝ)<a) (hc : 0<c) :
    Set.Icc a b ×ℂ Set.Icc c d ⊆ analyticContourDomain n := by
  intro z hz
  refine ⟨lt_of_lt_of_le ha hz.1.1,?_⟩
  rintro ⟨k,hk⟩
  have hi := congrArg Complex.im hk
  simp at hi
  have := hz.2.1
  linarith

theorem lowerRectangle_subset_analyticContourDomain (n : ℕ) (a b c d : ℝ)
    (hab : a≤b) (hcd : c≤d) (ha : ((67*n:ℕ):ℝ)<a) (hd : d<0) :
    Set.Icc a b ×ℂ Set.Icc c d ⊆ analyticContourDomain n := by
  intro z hz
  refine ⟨lt_of_lt_of_le ha hz.1.1,?_⟩
  rintro ⟨k,hk⟩
  have hi := congrArg Complex.im hk
  simp at hi
  have := hz.2.2
  linarith
end OddZeta.FourValue

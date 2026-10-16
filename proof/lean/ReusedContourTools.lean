import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

open MeasureTheory Set
namespace OddZeta.ContourTools

/-- Mathlib's reflection formula in the form needed by our contour kernel. -/
theorem gamma_reflection_kernel (t : ℂ) :
    Complex.Gamma (-t) * Complex.Gamma (1+t) =
      -(Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ)*t) := by
  have h := Complex.Gamma_mul_Gamma_one_sub (-t)
  simpa [sub_neg_eq_add, mul_neg, Complex.sin_neg, div_neg, neg_div] using h

/-- Four integrations by parts, retaining all endpoint terms.
The derivative assumptions concern the real parametrization of a contour. -/
theorem four_integrations_by_parts (a b : ℝ) (F K : ℕ → ℝ → ℂ)
    (hF : ∀ j < 4, ∀ x ∈ uIcc a b, HasDerivAt (F j) (F (j+1) x) x)
    (hK : ∀ j < 4, ∀ x ∈ uIcc a b, HasDerivAt (K j) (K (j+1) x) x)
    (iF : ∀ j, 1 ≤ j → j ≤ 4 → IntervalIntegrable (F j) volume a b)
    (iK : ∀ j, 1 ≤ j → j ≤ 4 → IntervalIntegrable (K j) volume a b) :
    (∫ x in a..b, F 4 x*K 0 x) =
      (F 3 b*K 0 b-F 2 b*K 1 b+F 1 b*K 2 b-F 0 b*K 3 b) -
      (F 3 a*K 0 a-F 2 a*K 1 a+F 1 a*K 2 a-F 0 a*K 3 a) +
      (∫ x in a..b, F 0 x*K 4 x) := by
  have h0 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (hK 0 (by norm_num)) (hF 3 (by norm_num))
    (iK 1 (by norm_num) (by norm_num)) (iF 4 (by norm_num) (by norm_num))
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (hK 1 (by norm_num)) (hF 2 (by norm_num))
    (iK 2 (by norm_num) (by norm_num)) (iF 3 (by norm_num) (by norm_num))
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (hK 2 (by norm_num)) (hF 1 (by norm_num))
    (iK 3 (by norm_num) (by norm_num)) (iF 2 (by norm_num) (by norm_num))
  have h3 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (hK 3 (by norm_num)) (hF 0 (by norm_num))
    (iK 4 (by norm_num) (by norm_num)) (iF 1 (by norm_num) (by norm_num))
  simp only [show (0:ℕ)+1=1 from rfl, show (1:ℕ)+1=2 from rfl,
    show (2:ℕ)+1=3 from rfl, show (3:ℕ)+1=4 from rfl, mul_comm] at h0 h1 h2 h3
  simp only [mul_comm]
  linear_combination h0-h1+h2-h3

#print axioms gamma_reflection_kernel
#print axioms four_integrations_by_parts
#print axioms Complex.integral_boundary_rect_eq_zero_of_differentiableOn
end OddZeta.ContourTools

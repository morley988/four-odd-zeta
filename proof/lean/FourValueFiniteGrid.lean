import FourValueWeightFractions
import FourValuePearsonBridge
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

/-! Finite Laurent-coefficient sums. Their Pearson identities hold for
every polynomial test, without a properness or degree assumption. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def rationalGrid (b : ℕ) (h : ℤ) : RatFunc K →ₗ[K] K :=
  ∑ j ∈ poleWindow b, rationalCoefficientAt (j:K) h

theorem rationalGrid_negative (b k : ℕ) :
    rationalGrid (K:=K) b (-(k:ℤ)) = rationalB b k := rfl

theorem integer_window_difference (b : ℕ) (f : ℤ → K) :
    (∑ j ∈ poleWindow b, (f j-f (j-1))) = f b-f (-(b:ℤ)-1) := by
  have ht := Finset.sum_Ico_int_sub b (fun j => f (j-1))
  have ht' : (∑ j ∈ Finset.Ico (-(b:ℤ)) b, (f j-f (j-1))) =
      f ((b:ℤ)-1)-f (-(b:ℤ)-1) := by
    simpa only [add_sub_cancel_right, ← Finset.sum_neg_distrib, neg_sub] using
      congrArg Neg.neg ht
  rw [poleWindow,Finset.sum_Icc_eq_sum_Ico_add _ (by omega),ht']
  ring

theorem rationalGrid_difference (b : ℕ) (h : ℤ) (f : RatFunc K) :
    rationalGrid b h (rationalDifference f) =
      rationalCoefficientAt (b:K) h f-rationalCoefficientAt (-(b:K)-1) h f := by
  simp only [rationalGrid,LinearMap.sum_apply,rationalDifference_apply,map_sub,
    rationalCoefficientAt_shift]
  convert integer_window_difference b (fun j => rationalCoefficientAt (j:K) h f) using 1
  · simp [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_neg_distrib,sub_eq_add_neg]
  · simp

theorem endpointDenominator_eval_left_boundary (b : ℕ) :
    (endpointDenominator (K:=K) b).eval (-(b:K)-1) ≠ 0 := by
  intro hz
  obtain ⟨j,hj,heq⟩ := (integerRootProduct_eval_zero_iff _ _).mp hz
  have heqZ : -(b:ℤ)-1=j := by exact_mod_cast heq
  simp only [Finset.mem_Ico] at hj
  omega

theorem pearsonBoundary_coeff_left_zero (b : ℕ) (a : Fin 15 → ℕ) (q : K[X])
    (h : ℕ) (hh : h<5) :
    rationalCoefficientAt (-(b:K)-1) h (pearsonBoundaryFunction b a q)=0 := by
  have heq : pearsonBoundaryNumerator b a q = (X-C (-(b:K)-1))^5 *
      (C (2^21:K)*(X-C (b:K))^5*q.comp ((C 2*X+1)^2)*tuplePadding b a) := by
    simp only [pearsonBoundaryNumerator,Nat.cast_add,Nat.cast_one,map_sub,map_neg,map_add,map_one]
    ring
  unfold pearsonBoundaryFunction
  rw [heq]
  apply rationalCoefficientAt_boundary_factor _ _ _ _ 5 h hh
  simpa using pow_ne_zero 10 (endpointDenominator_eval_left_boundary (K:=K) b)

theorem rationalGrid_pearson_difference_zero (b : ℕ) (a : Fin 15 → ℕ)
    (q : K[X]) (h : ℤ) (hh : h<5) :
    rationalGrid b h (rationalDifference (pearsonBoundaryFunction (K:=K) b a q))=0 := by
  rw [rationalGrid_difference]
  by_cases hn : h<0
  · have hr := rationalCoefficientAt_regular_neg (b:K)
      (pearsonBoundaryNumerator b a q) ((endpointDenominator b)^10)
      (by simpa using pow_ne_zero 10 (endpointDenominator_eval_boundary (K:=K) b)) h hn
    have hl := rationalCoefficientAt_regular_neg (-(b:K)-1)
      (pearsonBoundaryNumerator b a q) ((endpointDenominator b)^10)
      (by simpa using pow_ne_zero 10 (endpointDenominator_eval_left_boundary (K:=K) b)) h hn
    rw [show rationalCoefficientAt (b:K) h (pearsonBoundaryFunction b a q)=0 from hr,
      show rationalCoefficientAt (-(b:K)-1) h (pearsonBoundaryFunction b a q)=0 from hl,
      sub_self]
  · lift h to ℕ using (by omega : 0≤h)
    rw [pearsonBoundary_coeff_zero b a q h (by omega),
      pearsonBoundary_coeff_left_zero b a q h (by omega),sub_self]

def rawGridFunctional (b : ℕ) (a : Fin 15 → ℕ) (h : ℤ) : K[X] →ₗ[K] K where
  toFun p := rationalGrid b h (tupleEvenWeight b a *
    algebraMap K[X] (RatFunc K) (p.comp (C 2*X)))
  map_add' p q := by simp [Polynomial.add_comp,mul_add]
  map_smul' c p := by
    simp only [Polynomial.smul_comp,Polynomial.smul_eq_C_mul,Polynomial.mul_comp,Polynomial.C_comp,map_mul]
    rw [← mul_assoc, mul_comm (tupleEvenWeight b a), mul_assoc,
      RatFunc.algebraMap_C, ← RatFunc.smul_eq_C_mul, map_smul]
    rfl

/-- Antisymmetrization enforces oddness without any analytic kernel. -/
def finiteGridFunctional (b : ℕ) (a : Fin 15 → ℕ) (h : ℤ) : K[X] →ₗ[K] K where
  toFun p := (2:K)⁻¹ * (rawGridFunctional b a h p-
    rawGridFunctional b a h (p.comp (-X)))
  map_add' p q := by simp [Polynomial.add_comp]; ring
  map_smul' c p := by simp [Polynomial.smul_comp]; ring

theorem finiteGridFunctional_odd (b : ℕ) (a : Fin 15 → ℕ) (h : ℤ) (p : K[X]) :
    finiteGridFunctional b a h (p.comp (-X)) = -finiteGridFunctional b a h p := by
  simp only [finiteGridFunctional,LinearMap.coe_mk,AddHom.coe_mk,
    Polynomial.comp_neg_X_comp_neg_X]
  ring

theorem finiteGridFunctional_pearson (b : ℕ) (a : Fin 15 → ℕ)
    (ha : ∀ i,a i≤b) (h : ℤ) (hh : h<5) (q : K[X]) :
    finiteGridFunctional b a h (tuplePearsonPolynomial b a * q.comp ((X+1)^2))=0 := by
  have hp : rawGridFunctional b a h
      (tuplePearsonPolynomial b a * q.comp ((X+1)^2)) =
      rationalGrid b h (pearsonBoundaryFunction b a q) := by
    simp only [rawGridFunctional,LinearMap.coe_mk,AddHom.coe_mk,
      Polynomial.mul_comp,Polynomial.comp_assoc,Polynomial.pow_comp,
      Polynomial.add_comp,Polynomial.X_comp,Polynomial.one_comp,map_mul]
    rw [pearsonBoundaryFunction_physical b a q ha,mul_assoc]
  have hm : rawGridFunctional b a h
      ((tuplePearsonPolynomial b a * q.comp ((X+1)^2)).comp (-X)) =
      rationalGrid b h (rationalShift (-1) (pearsonBoundaryFunction b a q)) := by
    simp only [rawGridFunctional,LinearMap.coe_mk,AddHom.coe_mk,
      Polynomial.mul_comp,Polynomial.comp_assoc,Polynomial.pow_comp,
      Polynomial.add_comp,Polynomial.X_comp,Polynomial.one_comp,
      Polynomial.neg_comp,map_mul]
    rw [pearsonBoundaryFunction_shift_back b a q ha]
    have hs : (-(C 2*X)+1)^2=((C 2*X-1)^2 : K[X]) := by ring
    rw [hs,neg_mul,mul_assoc]
  change (2:K)⁻¹ * (_-_) = 0
  rw [hp,hm,← map_sub,← rationalDifference_apply,
    rationalGrid_pearson_difference_zero b a q h hh,mul_zero]

end OddZeta.FourValue

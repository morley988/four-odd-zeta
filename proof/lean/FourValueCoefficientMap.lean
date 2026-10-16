import FourValueZetaAssembly

noncomputable section
namespace OddZeta.FourValue
open Polynomial
open scoped LaurentSeries RatFunc
variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]

def coefficientRatFuncMap (f : K →+* L) : RatFunc K →+* RatFunc L :=
  RatFunc.mapRingHom (Polynomial.mapRingHom f)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective f f.injective))

theorem coefficientRatFuncMap_fraction (f : K →+* L) (p q : K[X]) :
    coefficientRatFuncMap f (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      algebraMap L[X] (RatFunc L) (p.map f) / algebraMap L[X] (RatFunc L) (q.map f) := by
  exact RatFunc.map_apply_div (Polynomial.mapRingHom f)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective f f.injective)) p q

theorem coefficientRatFuncMap_polynomial (f : K →+* L) (p : K[X]) :
    coefficientRatFuncMap f (algebraMap K[X] (RatFunc K) p) =
      algebraMap L[X] (RatFunc L) (p.map f) := by
  simpa using coefficientRatFuncMap_fraction f p 1

def coefficientLaurentMap (f : K →+* L) : K⸨X⸩ →+* L⸨X⸩ where
  toFun x := x.map f
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom

theorem coefficientLaurentMap_polynomial (f : K →+* L) (p : K[X]) :
    coefficientLaurentMap f (algebraMap K[X] K⸨X⸩ p) =
      algebraMap L[X] L⸨X⸩ (p.map f) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.map_add]
  | monomial n a =>
    ext j
    simp only [Polynomial.map_monomial]
    change f ((algebraMap K[X] K⸨X⸩ (monomial n a)).coeff j) = _
    by_cases hj : j < 0 <;> by_cases hn : j.natAbs = n <;> simp [PowerSeries.coeff_coe, hj, hn, PowerSeries.coeff_monomial, apply_ite]

theorem coefficientLaurentMap_ratFunc (f : K →+* L) (r : RatFunc K) :
    coefficientLaurentMap f (algebraMap (RatFunc K) K⸨X⸩ r) =
      algebraMap (RatFunc L) L⸨X⸩ (coefficientRatFuncMap f r) := by
  induction r using RatFunc.induction_on' with
  | _pq p q hq =>
    rw [RatFunc.mk_eq_div, coefficientRatFuncMap_fraction]
    simp only [map_div₀, ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩,
      ← IsScalarTower.algebraMap_apply L[X] (RatFunc L) L⸨X⸩,
      coefficientLaurentMap_polynomial]

theorem coefficientRatFuncMap_shift (f : K →+* L) (a : K) (r : RatFunc K) :
    coefficientRatFuncMap f (rationalShift a r) =
      rationalShift (f a) (coefficientRatFuncMap f r) := by
  induction r using RatFunc.induction_on' with
  | _pq p q hq =>
    simp only [RatFunc.mk_eq_div, rationalShift_fraction, coefficientRatFuncMap_fraction]
    congr 1 <;> congr 1 <;> simp [Polynomial.taylor, Polynomial.map_comp]

theorem rationalCoefficientAt_map (f : K →+* L) (a : K) (j : ℤ) (r : RatFunc K) :
    rationalCoefficientAt (f a) j (coefficientRatFuncMap f r) =
      f (rationalCoefficientAt a j r) := by
  change (algebraMap (RatFunc L) L⸨X⸩
    (rationalShift (f a) (coefficientRatFuncMap f r))).coeff j = _
  rw [← coefficientRatFuncMap_shift, ← coefficientLaurentMap_ratFunc]
  rfl
end OddZeta.FourValue

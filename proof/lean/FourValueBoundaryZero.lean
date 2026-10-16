import FourValueLaurentAtoms

noncomputable section
namespace OddZeta.FourValue
open Polynomial
open scoped LaurentSeries PowerSeries RatFunc
variable {K : Type*} [Field K] [CharZero K]

theorem rationalCoefficientAt_boundary_factor (a : K) (p q : K[X])
    (hq : q.eval a≠0) (r h : ℕ) (hh : h<r) :
    rationalCoefficientAt a h (algebraMap K[X] (RatFunc K) ((X-C a)^r*p) /
      algebraMap K[X] (RatFunc K) q)=0 := by
  change (rationalLaurentAt a _).coeff _ = _
  rw [rationalLaurentAt_regular a _ q hq,LaurentSeries.coeff_coe_powerSeries]
  simp only [Polynomial.taylor_mul,Polynomial.taylor_pow,map_sub,
    Polynomial.taylor_X,Polynomial.taylor_C,add_sub_cancel_right,
    Polynomial.coe_mul,Polynomial.coe_pow,Polynomial.coe_X]
  rw [mul_assoc,PowerSeries.coeff_X_pow_mul',if_neg (by omega)]

end OddZeta.FourValue

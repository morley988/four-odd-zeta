import FourValueLaurentObservations
import Mathlib.RingTheory.PowerSeries.WellKnown

noncomputable section
namespace OddZeta.FourValue
open Polynomial
open scoped LaurentSeries PowerSeries RatFunc
variable {K : Type*} [Field K] [CharZero K]

theorem rationalLaurentAt_polynomial (a : K) (p : K[X]) :
    rationalLaurentAt a (algebraMap K[X] (RatFunc K) p) =
      (((p.taylor a : K[X]) : K⟦X⟧) : K⸨X⸩) := by
  change algebraMap (RatFunc K) K⸨X⸩ (rationalShift a (algebraMap K[X] (RatFunc K) p)) = _
  rw [rationalShift_polynomial]
  rw [← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩]
  rfl

theorem rationalCoefficientAt_polynomial (a : K) (p : K[X]) (h : ℕ) :
    rationalCoefficientAt a h (algebraMap K[X] (RatFunc K) p)=(p.taylor a).coeff h := by
  change (rationalLaurentAt a _).coeff _ = _
  rw [rationalLaurentAt_polynomial,LaurentSeries.coeff_coe_powerSeries,Polynomial.coeff_coe]

theorem rationalCoefficientAt_polynomial_neg (a : K) (p : K[X]) (j : ℤ) (hj : j<0) :
    rationalCoefficientAt a j (algebraMap K[X] (RatFunc K) p)=0 := by
  change (rationalLaurentAt a _).coeff _ = _
  rw [rationalLaurentAt_polynomial,PowerSeries.coeff_coe,if_pos hj]

theorem powerSeries_inv_coe (f : K⟦X⟧) (hf : PowerSeries.constantCoeff f≠0) :
    ((f⁻¹ : K⟦X⟧) : K⸨X⸩)=(f:K⸨X⸩)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← PowerSeries.coe_mul,PowerSeries.inv_mul_cancel f hf,PowerSeries.coe_one]

theorem rationalLaurentAt_regular (a : K) (p q : K[X]) (hq : q.eval a≠0) :
    rationalLaurentAt a (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      (((((p.taylor a : K[X]):K⟦X⟧) * (((q.taylor a : K[X]):K⟦X⟧)⁻¹)) : K⟦X⟧) : K⸨X⸩) := by
  rw [map_div₀,rationalLaurentAt_polynomial,rationalLaurentAt_polynomial,PowerSeries.coe_mul,
    powerSeries_inv_coe]
  · rfl
  · simpa [Polynomial.constantCoeff_coe,Polynomial.taylor_coeff_zero] using hq

theorem rationalCoefficientAt_regular_neg (a : K) (p q : K[X]) (hq : q.eval a≠0)
    (j : ℤ) (hj : j<0) :
    rationalCoefficientAt a j (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q)=0 := by
  change (rationalLaurentAt a _).coeff _ = _
  rw [rationalLaurentAt_regular a p q hq,PowerSeries.coeff_coe,if_pos hj]

def rationalPole (a : K) (k : ℕ) : RatFunc K :=
  (algebraMap K[X] (RatFunc K) (X-C a))⁻¹ ^ k

theorem rationalPole_fraction (a : K) (k : ℕ) :
    rationalPole a k=algebraMap K[X] (RatFunc K) 1 /
      algebraMap K[X] (RatFunc K) ((X-C a)^k) := by
  simp [rationalPole,div_eq_mul_inv,inv_pow]

theorem rationalPole_shift (a t : K) (k : ℕ) :
    rationalShift t (rationalPole a k)=rationalPole (a-t) k := by
  rw [rationalPole_fraction,rationalShift_fraction,rationalPole_fraction]
  simp only [map_one,Polynomial.taylor_one,Polynomial.C_1,Polynomial.taylor_pow,
    map_sub,Polynomial.taylor_X,Polynomial.taylor_C]
  congr 3 <;> ring

theorem rationalLaurentAt_pole_self (a : K) (k : ℕ) :
    rationalLaurentAt a (rationalPole a k)=HahnSeries.single (-(k:ℤ)) (1:K) := by
  change algebraMap (RatFunc K) K⸨X⸩ (rationalShift a (rationalPole a k)) = _
  rw [rationalPole_shift,sub_self]
  simp only [rationalPole,map_zero,sub_zero,map_pow,map_inv₀,RatFunc.algebraMap_X,
    RatFunc.coe_X,HahnSeries.inv_single,inv_one]
  simp

theorem rationalCoefficientAt_pole_self (a : K) (k : ℕ) (j : ℤ) :
    rationalCoefficientAt a j (rationalPole a k)=if j=-(k:ℤ) then 1 else 0 := by
  change (rationalLaurentAt a _).coeff _ = _
  rw [rationalLaurentAt_pole_self,HahnSeries.coeff_single]
  split_ifs <;> rfl

theorem rationalCoefficientAt_pole_other_neg (a t : K) (k : ℕ) (hat : t≠a)
    (j : ℤ) (hj : j<0) : rationalCoefficientAt t j (rationalPole a k)=0 := by
  rw [rationalPole_fraction]
  apply rationalCoefficientAt_regular_neg t 1 ((X-C a)^k) _ j hj
  simpa using pow_ne_zero k (sub_ne_zero.mpr hat)

end OddZeta.FourValue

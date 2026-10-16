import FourValueLaurentAtoms

noncomputable section
namespace OddZeta.FourValue
open Polynomial
open scoped LaurentSeries PowerSeries RatFunc
variable {K : Type*} [Field K] [CharZero K]

def poleTaylorSeries (d : K) (k : ℕ) : K⟦X⟧ :=
  PowerSeries.C (d⁻¹^k) * PowerSeries.rescale (-d⁻¹) (PowerSeries.invOneSubPow K k).val

theorem poleTaylorSeries_mul (d : K) (hd : d≠0) (k : ℕ) :
    poleTaylorSeries d k * (PowerSeries.X+PowerSeries.C d)^k=1 := by
  have hp := congrArg (PowerSeries.rescale (-d⁻¹)) (PowerSeries.invOneSubPow K k).val_inv
  rw [map_mul,PowerSeries.invOneSubPow_inv_eq_one_sub_pow,map_pow,map_sub,map_one,
    PowerSeries.rescale_X] at hp
  have hD : (PowerSeries.X+PowerSeries.C d : K⟦X⟧)=
      PowerSeries.C d*(1-PowerSeries.C (-d⁻¹)*PowerSeries.X) := by
    have hc : PowerSeries.C d * PowerSeries.C (-d⁻¹) = (-1:K⟦X⟧) := by
      rw [← map_mul,mul_neg,mul_inv_cancel₀ hd,map_neg,map_one]
    rw [mul_sub,mul_one,← mul_assoc,hc,neg_one_mul,sub_neg_eq_add,add_comm]
  rw [poleTaylorSeries,hD,mul_pow]
  calc
    _ = (PowerSeries.C (d⁻¹^k)*PowerSeries.C d^k)*
        (PowerSeries.rescale (-d⁻¹) (PowerSeries.invOneSubPow K k).val*
          (1-PowerSeries.C (-d⁻¹)*PowerSeries.X)^k) := by ring
    _ = 1 := by rw [hp,← map_pow,← map_mul,← mul_pow,inv_mul_cancel₀ hd,one_pow,map_one,mul_one]

theorem poleTaylorSeries_coeff (d : K) (k h : ℕ) :
    PowerSeries.coeff h (poleTaylorSeries d (k+1)) =
      (-1:K)^h * (Nat.choose (k+h) h:K) / d^(k+h+1) := by
  rw [poleTaylorSeries,PowerSeries.coeff_C_mul,PowerSeries.coeff_rescale,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,PowerSeries.coeff_mk,Nat.choose_symm_add]
  rw [neg_pow]
  simp only [div_eq_mul_inv,inv_pow]
  rw [show k+h+1=(k+1)+h by omega,pow_add]
  ring

theorem rationalLaurentAt_pole_regular (a t : K) (hat : t≠a) (k : ℕ) :
    rationalLaurentAt t (rationalPole a k)=(poleTaylorSeries (t-a) k : K⸨X⸩) := by
  have hd : t-a≠0 := sub_ne_zero.mpr hat
  have hmul := congrArg (fun f : K⟦X⟧ => (f:K⸨X⸩)) (poleTaylorSeries_mul (t-a) hd k)
  rw [PowerSeries.coe_mul,PowerSeries.coe_pow,PowerSeries.coe_add,PowerSeries.coe_X,
    PowerSeries.coe_C,PowerSeries.coe_one] at hmul
  have heq := eq_inv_of_mul_eq_one_left hmul
  rw [heq]
  change algebraMap (RatFunc K) K⸨X⸩ (rationalShift t (rationalPole a k)) = _
  rw [rationalPole_shift]
  simp only [rationalPole,map_pow,map_inv₀,map_sub,RatFunc.algebraMap_X,RatFunc.coe_X]
  have hc (c : K) : algebraMap (RatFunc K) K⸨X⸩ (algebraMap K[X] (RatFunc K) (C c)) =
      HahnSeries.C c := by
    rw [← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩]
    simp
  simp only [hc,inv_pow,map_sub]
  congr 2
  ring

theorem rationalCoefficientAt_pole_regular (a t : K) (hat : t≠a) (k h : ℕ) :
    rationalCoefficientAt t h (rationalPole a (k+1)) =
      (-1:K)^h*(Nat.choose (k+h) h:K)/(t-a)^(k+h+1) := by
  change (rationalLaurentAt t _).coeff _ = _
  rw [rationalLaurentAt_pole_regular a t hat,LaurentSeries.coeff_coe_powerSeries,poleTaylorSeries_coeff]

end OddZeta.FourValue

import FourValueGridFiniteness
import FourValueSeedPoles

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem finiteGridFunctional_on_odd (b : ℕ) (a : Fin 15 → ℕ) (h : ℤ)
    (p : K[X]) (hp : p.comp (-X) = -p) :
    finiteGridFunctional b a h p=rawGridFunctional b a h p := by
  change (2:K)⁻¹ * (_-_) = _
  rw [hp,map_neg]
  field_simp
  ring

theorem finiteGridFunctional_lift (b : ℕ) (a : Fin 15 → ℕ) (h : ℤ) (p : K[X]) :
    finiteGridFunctional b a h (X*p.comp (X^2)) =
      2*rationalGrid b h (tupleRationalTest b a (p.comp (C 4*X))) := by
  rw [finiteGridFunctional_on_odd]
  · change rationalGrid b h (tupleEvenWeight b a *
      algebraMap K[X] (RatFunc K) ((X*p.comp (X^2)).comp (C 2*X))) = _
    have heq : tupleEvenWeight b a *
        algebraMap K[X] (RatFunc K) ((X*p.comp (X^2)).comp (C 2*X)) =
        (2:K) • tupleRationalTest b a (p.comp (C 4*X)) := by
      change _ = (2:K) • (tupleWeight b a * algebraMap K[X] (RatFunc K)
        ((p.comp (C 4*X)).comp (X^2)))
      rw [tupleWeight_eq_X_even,RatFunc.smul_eq_C_mul]
      simp only [Polynomial.mul_comp,Polynomial.X_comp,Polynomial.comp_assoc,
        Polynomial.pow_comp,Polynomial.C_comp,map_mul,RatFunc.algebraMap_C,RatFunc.algebraMap_X]
      have hs : (C 2*X)^2=(C 4*X^2 : K[X]) := by rw [map_ofNat,map_ofNat]; ring
      rw [hs]
      ring
    rw [heq,map_smul,smul_eq_mul]
  · simp only [Polynomial.mul_comp,Polynomial.comp_assoc,Polynomial.pow_comp,
      Polynomial.X_comp,neg_pow_two,Polynomial.comp_X,neg_mul]

theorem finiteGridFunctional_negative_lift (b k : ℕ) (a : Fin 15 → ℕ) (p : K[X]) :
    finiteGridFunctional b a (-(k:ℤ)) (X*p.comp (X^2)) =
      2*concreteB b a k (p.comp (C 4*X)) := by
  rw [finiteGridFunctional_lift,rationalGrid_negative]
  rfl

end OddZeta.FourValue

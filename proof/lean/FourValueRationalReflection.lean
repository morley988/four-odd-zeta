import FourValueGridFiniteness

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def rationalReflect : RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.mapAlgHom Polynomial.algEquivAevalNegX.toAlgHom
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      Polynomial.algEquivAevalNegX.injective)

theorem rationalReflect_fraction (p q : K[X]) :
    rationalReflect (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      algebraMap K[X] (RatFunc K) (p.comp (-X)) /
      algebraMap K[X] (RatFunc K) (q.comp (-X)) := by
  exact RatFunc.map_apply_div Polynomial.algEquivAevalNegX.toAlgHom
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      Polynomial.algEquivAevalNegX.injective) p q

theorem rationalReflect_polynomial (p : K[X]) :
    rationalReflect (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (p.comp (-X)) := by
  simpa using rationalReflect_fraction p 1

theorem rationalReflect_pole (t : K) (k : ℕ) :
    rationalReflect (rationalPole t k)=(-1:K)^k • rationalPole (-t) k := by
  unfold rationalPole
  rw [map_pow,map_inv₀,rationalReflect_polynomial]
  have heq : (X-C t).comp (-X)=-(X-C (-t)) := by simp; ring
  rw [heq,map_neg,inv_neg,neg_pow,RatFunc.smul_eq_C_mul]
  simp only [map_pow,map_neg,map_one]

theorem centeredDenominator_reflect (b : ℕ) :
    (centeredDenominator (K:=K) b).comp (-X) = -centeredDenominator b := by
  induction b with
  | zero => simp
  | succ b ih =>
    simp only [centeredDenominator_succ,Polynomial.mul_comp,Polynomial.sub_comp,
      Polynomial.pow_comp,Polynomial.X_comp,Polynomial.C_comp,neg_pow_two,ih,neg_mul]

theorem tupleDenominator_reflect (a : Fin 15 → ℕ) :
    (tupleDenominator (K:=K) a).comp (-X) = -tupleDenominator a := by
  simp [tupleDenominator,Polynomial.prod_comp,centeredDenominator_reflect,Finset.prod_neg]
  ring

theorem tupleEvenWeight_reflect (b : ℕ) (a : Fin 15 → ℕ) :
    rationalReflect (tupleEvenWeight (K:=K) b a)=tupleEvenWeight b a := by
  unfold tupleEvenWeight
  rw [rationalReflect_fraction]
  simp [Polynomial.mul_comp,Polynomial.pow_comp,centeredDenominator_reflect,
    tupleDenominator_reflect]
  ring

theorem tupleRationalTest_reflect (b : ℕ) (a : Fin 15 → ℕ) (p : K[X]) :
    rationalReflect (tupleRationalTest b a p) = -tupleRationalTest b a p := by
  change rationalReflect (tupleWeight b a*algebraMap K[X] (RatFunc K) (p.comp (X^2))) = _
  rw [tupleWeight_eq_X_even,map_mul,map_mul,tupleEvenWeight_reflect]
  have hx : rationalReflect (RatFunc.X:RatFunc K) = -RatFunc.X := by
    simpa using rationalReflect_polynomial (X:K[X])
  rw [hx,rationalReflect_polynomial]
  simp only [Polynomial.comp_assoc,Polynomial.pow_comp,Polynomial.X_comp,
    neg_pow_two,neg_mul]
  change _ = -(tupleWeight b a * _)
  rw [tupleWeight_eq_X_even]

end OddZeta.FourValue

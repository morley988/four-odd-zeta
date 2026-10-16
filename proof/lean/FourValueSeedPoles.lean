import FourValueConcretePearson

noncomputable section
namespace OddZeta.FourValue
open Polynomial
open scoped LaurentSeries PowerSeries RatFunc
variable {K : Type*} [Field K] [CharZero K]

theorem rationalCoefficientAt_pole_mul (a : K) (k : ℕ) (f : RatFunc K) (j : ℤ) :
    rationalCoefficientAt a j (rationalPole a k*f)=rationalCoefficientAt a (j+k) f := by
  change (rationalLaurentAt a _).coeff _ = _
  rw [map_mul,rationalLaurentAt_pole_self,HahnSeries.coeff_single_mul,one_mul]
  simp only [sub_neg_eq_add]
  rfl

def seedCentralUnit (b : ℕ) : K[X] :=
  ∏ j ∈ Finset.range b,(X^2-C (((j+1:ℕ):K)^2))

theorem seedCentralUnit_factor (b : ℕ) :
    centeredDenominator (K:=K) b=X*seedCentralUnit b := centeredDenominator_product b

theorem seedCentralUnit_eval_zero (b : ℕ) : (seedCentralUnit (K:=K) b).eval 0≠0 := by
  simp only [seedCentralUnit,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_C,zero_pow (by omega : 2≠0),zero_sub,
    Finset.prod_ne_zero_iff,neg_ne_zero,pow_ne_zero_iff (by omega : 2≠0)]
  intro j hj
  exact Nat.cast_ne_zero.mpr (by omega)

theorem seed_test_other_poles (b : ℕ) (p : K[X]) (j : ℤ) (hj : j∈poleWindow b)
    (hj0 : j≠0) (k : ℕ) (hk : 2≤k) :
    rationalCoefficientAt (j:K) (-(k:ℤ)) (tupleRationalTest b (seedTuple b) p)=0 := by
  classical
  let E : K[X] := integerRootProduct ((poleWindow b).erase j)
  have hfac : centeredDenominator (K:=K) b=(X-C (j:K))*E := by
    rw [centeredDenominator_integerProduct,integerRootProduct]
    exact (Finset.mul_prod_erase _ _ hj).symm
  have hE : E.eval (j:K)≠0 := by
    intro hz
    obtain ⟨i,hi,hij⟩ := (integerRootProduct_eval_zero_iff _ _).mp hz
    exact (Finset.mem_erase.mp hi).1 (Int.cast_injective hij.symm)
  have hq : (X^8*E).eval (j:K)≠0 := by
    simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X]
    exact mul_ne_zero (pow_ne_zero _ (Int.cast_ne_zero.mpr hj0)) hE
  have heq : tupleRationalTest b (seedTuple b) p = rationalPole (j:K) 1 *
      (algebraMap K[X] (RatFunc K) (C 2*p.comp (X^2)) /
        algebraMap K[X] (RatFunc K) (X^8*E)) := by
    change tupleWeight b (seedTuple b)*_= _
    rw [tupleWeight_seed,hfac]
    simp only [map_mul,map_pow,rationalPole,pow_one,map_ofNat,Polynomial.C_ofNat]
    ring
  rw [heq,rationalCoefficientAt_pole_mul]
  exact rationalCoefficientAt_regular_neg _ _ _ hq _ (by omega)

set_option maxHeartbeats 1000000 in
theorem seed_B_center (b : ℕ) (p : K[X]) (k : ℕ) (hk : 2≤k) :
    rationalB b k (tupleRationalTest b (seedTuple b) p)=
      rationalCoefficientAt (0:K) (-(k:ℤ)) (tupleRationalTest b (seedTuple b) p) := by
  classical
  simp only [rationalB,LinearMap.sum_apply]
  rw [Finset.sum_eq_single (0:ℤ)]
  · simp only [Int.cast_zero]
  · intro j hj hj0
    exact seed_test_other_poles b p j hj hj0 k hk
  · intro h
    exact False.elim (h (by simp [poleWindow]))

theorem seed_test_small_monomial (b : ℕ) (i : Fin 4) :
    tupleRationalTest (K:=K) b (seedTuple b) (X^i.val) =
      rationalPole 0 (9-2*i.val) *
      (algebraMap K[X] (RatFunc K) (C 2) /
        algebraMap K[X] (RatFunc K) (seedCentralUnit b)) := by
  change tupleWeight b (seedTuple b)*_= _
  rw [tupleWeight_seed,seedCentralUnit_factor]
  simp only [Polynomial.pow_comp,Polynomial.X_comp,map_pow,map_mul,rationalPole,map_zero,
    sub_zero]
  have hX : algebraMap K[X] (RatFunc K) X≠0 := RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have he : 9-2*i.val+2*i.val=9 := by omega
  have hU : algebraMap K[X] (RatFunc K) (seedCentralUnit (K:=K) b)≠0 := by
    apply RatFunc.algebraMap_ne_zero
    intro hz
    exact seedCentralUnit_eval_zero (K:=K) b (by rw [hz]; simp)
  simp only [Polynomial.C_ofNat,map_ofNat]
  rw [← pow_mul, inv_pow]
  field_simp
  rw [← pow_add]
  congr 1
  omega

theorem rationalCoefficientAt_regular_zero (a : K) (p q : K[X]) (hq : q.eval a≠0) :
    rationalCoefficientAt a 0 (algebraMap K[X] (RatFunc K) p /
      algebraMap K[X] (RatFunc K) q)=p.eval a/q.eval a := by
  change (rationalLaurentAt a _).coeff 0= _
  rw [rationalLaurentAt_regular a p q hq]
  rw [show (0:ℤ)=((0:ℕ):ℤ) from rfl,LaurentSeries.coeff_coe_powerSeries]
  simp [PowerSeries.coeff_zero_eq_constantCoeff,Polynomial.constantCoeff_coe,
    Polynomial.taylor_coeff_zero,div_eq_mul_inv]

def seedBMatrix (b : ℕ) : Matrix (Fin 4) (Fin 4) K :=
  fun i j => rationalB b (9-2*i.val) (tupleRationalTest b (seedTuple b) (X^j.val))

theorem seedBMatrix_above (b : ℕ) (i j : Fin 4) (hij : i<j) :
    seedBMatrix (K:=K) b i j=0 := by
  rw [seedBMatrix,seed_B_center b _ _ (by omega),seed_test_small_monomial,
    rationalCoefficientAt_pole_mul]
  exact rationalCoefficientAt_regular_neg _ _ _ (seedCentralUnit_eval_zero b) _ (by
    have := i.isLt
    have := j.isLt
    omega)

theorem seedBMatrix_diagonal (b : ℕ) (i : Fin 4) :
    seedBMatrix (K:=K) b i i=2/(seedCentralUnit b).eval 0 := by
  rw [seedBMatrix,seed_B_center b _ _ (by omega),seed_test_small_monomial,
    rationalCoefficientAt_pole_mul,neg_add_cancel,
    rationalCoefficientAt_regular_zero _ _ _ (seedCentralUnit_eval_zero b)]
  simp

theorem seedBMatrix_isUnit (b : ℕ) : IsUnit (seedBMatrix (K:=K) b) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply IsUnit.mk0
  rw [← Matrix.det_transpose,Matrix.det_of_isUpperTriangular
    (show (seedBMatrix (K:=K) b).transpose.IsUpperTriangular from
      fun i j hij => seedBMatrix_above b j i hij)]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  change seedBMatrix b i i≠0
  rw [seedBMatrix_diagonal]
  exact div_ne_zero (by norm_num) (seedCentralUnit_eval_zero b)

end OddZeta.FourValue

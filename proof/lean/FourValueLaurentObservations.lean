import Mathlib.Tactic
import Mathlib.RingTheory.LaurentSeries

noncomputable section
namespace OddZeta.FourValue
open Polynomial
open scoped LaurentSeries PowerSeries RatFunc
variable {K : Type*} [Field K] [CharZero K]

def rationalShift (a : K) : RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.mapAlgHom (Polynomial.taylorAlgHom a)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (Polynomial.taylor_injective a))

theorem rationalShift_fraction (a : K) (p q : K[X]) :
    rationalShift a (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      algebraMap K[X] (RatFunc K) (p.taylor a) / algebraMap K[X] (RatFunc K) (q.taylor a) := by
  exact RatFunc.map_apply_div (Polynomial.taylorAlgHom a)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (Polynomial.taylor_injective a)) p q

theorem rationalShift_polynomial (a : K) (p : K[X]) :
    rationalShift a (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (p.taylor a) := by
  simpa using rationalShift_fraction a p 1

theorem rationalShift_add (a b : K) (f : RatFunc K) :
    rationalShift a (rationalShift b f)=rationalShift (a+b) f := by
  induction f using RatFunc.induction_on' with
  | _pq p q hq => simp only [RatFunc.mk_eq_div,rationalShift_fraction,Polynomial.taylor_taylor]

theorem rationalShift_zero (f : RatFunc K) : rationalShift 0 f=f := by
  induction f using RatFunc.induction_on' with
  | _pq p q hq => simp only [RatFunc.mk_eq_div,rationalShift_fraction,Polynomial.taylor_zero]

def rationalLaurentAt (a : K) : RatFunc K →+* K⸨X⸩ :=
  (algebraMap (RatFunc K) K⸨X⸩).comp (rationalShift a).toRingHom

theorem rationalLaurentAt_C (a c : K) :
    rationalLaurentAt a (RatFunc.C c)=HahnSeries.C c := by
  change algebraMap (RatFunc K) K⸨X⸩ (rationalShift a (algebraMap K[X] (RatFunc K) (C c))) = _
  rw [rationalShift_polynomial,Polynomial.taylor_C]
  rw [← IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩]
  simp

def rationalCoefficientAt (a : K) (j : ℤ) : RatFunc K →ₗ[K] K where
  toFun f := (rationalLaurentAt a f).coeff j
  map_add' f g := by simp
  map_smul' c f := by
    change (rationalLaurentAt a (c • f)).coeff j = c * (rationalLaurentAt a f).coeff j
    rw [RatFunc.smul_eq_C_mul,map_mul,rationalLaurentAt_C]
    simp

theorem rationalCoefficientAt_shift (a b : K) (j : ℤ) (f : RatFunc K) :
    rationalCoefficientAt a j (rationalShift b f)=rationalCoefficientAt (a+b) j f := by
  change (algebraMap (RatFunc K) K⸨X⸩ (rationalShift a (rationalShift b f))).coeff j = _
  rw [rationalShift_add]
  rfl

def poleWindow (b : ℕ) : Finset ℤ := Finset.Icc (-(b:ℤ)) b

def rationalB (b k : ℕ) : RatFunc K →ₗ[K] K :=
  ∑ j ∈ poleWindow b, rationalCoefficientAt (j:K) (-(k:ℤ))

def finiteHarmonic (m s : ℕ) : K := ∑ r ∈ Finset.range m, 1/((r+1:ℕ):K)^s

def rationalC (b h : ℕ) : RatFunc K →ₗ[K] K :=
  -(-1:K)^h • ∑ j ∈ poleWindow b, ∑ k ∈ Finset.range 10,
    ((Nat.choose (k+h) h:K)*finiteHarmonic ((b-j).toNat) (k+h+1)) •
      rationalCoefficientAt (j:K) (-((k+1:ℕ):ℤ))

def nineRationalObservations (b : ℕ) : Fin 9 → RatFunc K →ₗ[K] K :=
  ![rationalB b 3, rationalB b 5, rationalB b 7, rationalB b 9,
    rationalC b 0, rationalC b 1, rationalC b 2, rationalC b 3, rationalC b 4]

end OddZeta.FourValue

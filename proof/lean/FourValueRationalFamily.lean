import FourValueCenteredProducts
import FourValueTuplePearson
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic

/-! The actual unnormalized rational weight and its endpoint transition.
The coefficient functionals are still to be identified on this family. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def tupleDenominator (a : Fin 15 → ℕ) : K[X] := ∏ i, centeredDenominator (a i)

def tupleNumerator (b : ℕ) : K[X] := C 2*X*(centeredDenominator b)^5

def tupleWeight (b : ℕ) (a : Fin 15 → ℕ) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (tupleNumerator b) /
    algebraMap K[X] (RatFunc K) (tupleDenominator a)

theorem tupleDenominator_monic (a : Fin 15 → ℕ) : (tupleDenominator (K:=K) a).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun i _ => centeredDenominator_monic (a i))

theorem tupleDenominator_degree (a : Fin 15 → ℕ) :
    (tupleDenominator (K:=K) a).natDegree=2*(∑ i,a i)+15 := by
  rw [tupleDenominator,Polynomial.natDegree_prod_of_monic _ _
    (fun i _ => centeredDenominator_monic (a i))]
  simp only [centeredDenominator_degree,Finset.sum_add_distrib,← Finset.mul_sum]
  simp

theorem tupleNumerator_ne_zero (b : ℕ) : tupleNumerator (K:=K) b≠0 := by
  exact mul_ne_zero (mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num)) Polynomial.X_ne_zero)
    (pow_ne_zero _ (centeredDenominator_monic b).ne_zero)

theorem tupleNumerator_degree (b : ℕ) :
    (tupleNumerator (K:=K) b).natDegree=10*b+6 := by
  rw [tupleNumerator,Polynomial.natDegree_mul
    (mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num)) Polynomial.X_ne_zero)
    (pow_ne_zero _ (centeredDenominator_monic b).ne_zero),
    Polynomial.natDegree_C_mul (by norm_num : (2:K)≠0),Polynomial.natDegree_X,
    Polynomial.natDegree_pow,centeredDenominator_degree]
  omega

theorem tuple_degree_gap (b : ℕ) (a : Fin 15 → ℕ) :
    ((tupleDenominator (K:=K) a).natDegree:ℤ)-(tupleNumerator (K:=K) b).natDegree=
      2*tupleBeta b a+9 := by
  rw [tupleDenominator_degree,tupleNumerator_degree,tupleBeta]
  push_cast
  ring

theorem tupleDenominator_update_succ (a : Fin 15 → ℕ) (i : Fin 15) :
    tupleDenominator (K:=K) (Function.update a i (a i+1)) =
      tupleDenominator a*(X^2-C (((a i+1:ℕ):K)^2)) := by
  classical
  let a' := Function.update a i (a i+1)
  have hprod : (∏ j ∈ Finset.univ.erase i, centeredDenominator (K:=K) (a' j)) =
      ∏ j ∈ Finset.univ.erase i, centeredDenominator (K:=K) (a j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j≠i := (Finset.mem_erase.mp hj).1
    simp [a',hji]
  rw [tupleDenominator,← Finset.mul_prod_erase _ _ (Finset.mem_univ i),hprod]
  simp only [Function.update_self]
  rw [centeredDenominator_succ]
  rw [show tupleDenominator (K:=K) a = centeredDenominator (a i)*
      ∏ j ∈ Finset.univ.erase i, centeredDenominator (a j) from
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm]
  ring

theorem tupleWeight_endpoint_step (b : ℕ) (a : Fin 15 → ℕ) (i : Fin 15) :
    tupleWeight (K:=K) b (Function.update a i (a i+1)) *
      algebraMap K[X] (RatFunc K) (X^2-C (((a i+1:ℕ):K)^2)) = tupleWeight b a := by
  have hD : algebraMap K[X] (RatFunc K) (tupleDenominator (K:=K) a)≠0 :=
    RatFunc.algebraMap_ne_zero (tupleDenominator_monic a).ne_zero
  have hF : algebraMap K[X] (RatFunc K) (X^2-C (((a i+1:ℕ):K)^2))≠0 := by
    apply RatFunc.algebraMap_ne_zero
    have hf : (X^2-C (((a i+1:ℕ):K)^2):K[X])=
        (X-C ((a i+1:ℕ):K))*(X+C ((a i+1:ℕ):K)) := by simp only [map_pow]; ring
    rw [hf]
    exact ((Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_add_C _)).ne_zero
  rw [tupleWeight,tupleDenominator_update_succ,map_mul,tupleWeight]
  field_simp

def tupleRationalTest (b : ℕ) (a : Fin 15 → ℕ) : K[X] →ₗ[K] RatFunc K where
  toFun p := tupleWeight b a * algebraMap K[X] (RatFunc K) (p.comp (X^2))
  map_add' p q := by simp [Polynomial.add_comp,mul_add]
  map_smul' c p := by
    rw [Polynomial.smul_comp,Polynomial.smul_eq_C_mul,map_mul]
    rw [show algebraMap K[X] (RatFunc K) (C c)=algebraMap K (RatFunc K) c from
      (IsScalarTower.algebraMap_apply K K[X] (RatFunc K) c).symm]
    simp only [Algebra.smul_def,RingHom.id_apply]
    ring

/-- Decreasing an endpoint multiplies the actual test weight by the
corresponding squared-coordinate factor, exactly as needed by the companion step. -/
theorem tupleRationalTest_endpoint_step (b : ℕ) (a : Fin 15 → ℕ) (i : Fin 15) (p : K[X]) :
    tupleRationalTest b (Function.update a i (a i+1))
      ((X-C (((a i+1:ℕ):K)^2))*p) = tupleRationalTest b a p := by
  change tupleWeight b (Function.update a i (a i+1)) *
      algebraMap K[X] (RatFunc K) (((X-C (((a i+1:ℕ):K)^2))*p).comp (X^2)) = _
  simp only [Polynomial.mul_comp,Polynomial.sub_comp,Polynomial.X_comp,Polynomial.C_comp,map_mul]
  rw [← mul_assoc,tupleWeight_endpoint_step]
  rfl

end OddZeta.FourValue

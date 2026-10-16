import FourValueSeedObservations
import FourValueSeedJets

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def seedNumeratorMap (b : ℕ) : K[X] →ₗ[K] RatFunc K where
  toFun p := algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) (centeredDenominator b)
  map_add' p q := by simp [add_div]
  map_smul' c p := by
    rw [Polynomial.smul_eq_C_mul,map_mul]
    rw [show algebraMap K[X] (RatFunc K) (C c)=algebraMap K (RatFunc K) c from
      (IsScalarTower.algebraMap_apply K K[X] (RatFunc K) c).symm]
    simp [Algebra.smul_def,mul_div_assoc]

theorem seed_test_tail_monomial (b : ℕ) (l : ℕ) :
    tupleRationalTest (K:=K) b (seedTuple b) (X^(l+4)) =
      seedNumeratorMap b ((2:K) • X^(2*l)) := by
  change tupleWeight b (seedTuple b)*_ = _
  rw [tupleWeight_seed]
  change _ = algebraMap K[X] (RatFunc K) ((2:K) • X^(2*l)) / _
  simp only [Polynomial.pow_comp,Polynomial.X_comp,Polynomial.smul_eq_C_mul,map_mul,
    Polynomial.C_ofNat,map_ofNat,map_pow]
  have hX : algebraMap K[X] (RatFunc K) X≠0 := RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have hD := RatFunc.algebraMap_ne_zero (K:=K) (centeredDenominator_monic (K:=K) b).ne_zero
  field_simp
  ring

theorem seed_tail_B_zero (b : ℕ) (hb : 5≤b) (l : Fin 5) (k : ℕ) (hk : 0<k) :
    rationalB (K:=K) b k (tupleRationalTest b (seedTuple b) (X^(l.val+4)))=0 := by
  obtain ⟨c,hc,_⟩ := seedAntidifference_monomial (b:K) (seed_natural_parameter b hb) l
  rw [seed_test_tail_monomial,← hc]
  change rationalB b k (algebraMap K[X] (RatFunc K) _ / _)=0
  rw [← seedBoundaryFunction_difference]
  exact seedBoundaryFunction_B b hb _ (seedPolynomial_degree c) k hk

theorem seed_tail_C_kernel (b : ℕ) (hb : 5≤b) (v : Fin 5 → K)
    (hz : ∀ h : Fin 5, ∑ l : Fin 5,v l *
      rationalC (K:=K) b h.val (tupleRationalTest b (seedTuple b) (X^(l.val+4)))=0) :
    v=0 := by
  obtain ⟨c,hc,_⟩ := seedAntidifference_exists_unique (b:K) (seed_natural_parameter b hb)
    (fun i => 2*v i)
  have hf : rationalDifference (seedBoundaryFunction b (seedPolynomial c))=
      ∑ l : Fin 5,v l • tupleRationalTest b (seedTuple b) (X^(l.val+4)) := by
    rw [seedBoundaryFunction_difference]
    change seedNumeratorMap b (seedAntidifference (b:K) (seedPolynomial c))= _
    rw [hc]
    simp only [seedEvenPolynomial,map_sum,map_smul,seed_test_tail_monomial,map_smul,smul_smul]
    apply Finset.sum_congr rfl
    intro l _
    rw [mul_comm]
  have hj : ∀ h : Fin 5, ((seedPolynomial c).taylor ((b:K)+1)).coeff h.val=0 := by
    intro h
    have hzero : ∀ (i : ℕ), i<5 → rationalCoefficientAt (b:K) i
        (algebraMap K[X] (RatFunc K) ((seedPolynomial c).taylor 1) /
          algebraMap K[X] (RatFunc K) (endpointDenominator b))=0 := by
      intro i hi
      rw [← seedBoundaryFunction_C b hb _ (seedPolynomial_degree c) i,hf,map_sum]
      simpa only [map_smul,smul_eq_mul] using hz ⟨i,hi⟩
    have hh := rational_regular_zero_jets (b:K) ((seedPolynomial c).taylor 1)
      (endpointDenominator b) (endpointDenominator_eval_boundary b) 5 hzero h.val h.isLt
    simpa only [Polynomial.taylor_taylor] using hh
  have hc0 := seedPolynomial_zero_of_jets b c hj
  have hev : seedEvenPolynomial (fun i => 2*v i)=0 := by
    rw [← hc,hc0]
    simp [seedPolynomial]
  have hv : (fun i => 2*v i)=(0:Fin 5 → K) := seedEvenPolynomial_injective
    (by simpa [seedEvenPolynomial] using hev)
  funext i
  have hi := congrFun hv i
  simpa using hi

end OddZeta.FourValue

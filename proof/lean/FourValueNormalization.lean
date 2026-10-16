import FourValueSeedIndependence

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- Scalar normalization of the actual rational weight. -/
def normalizedTupleTest (s : K) (b : ℕ) (a : Fin 15 → ℕ) : K[X] →ₗ[K] RatFunc K :=
  s • tupleRationalTest b a

theorem normalizedTupleTest_apply (s : K) (b : ℕ) (a : Fin 15 → ℕ) (p : K[X]) :
    normalizedTupleTest s b a p = s • tupleRationalTest b a p := rfl

theorem normalizedTupleTest_weight (s : K) (b : ℕ) (a : Fin 15 → ℕ) (p : K[X]) :
    normalizedTupleTest s b a p =
      (RatFunc.C s * tupleWeight b a) * algebraMap K[X] (RatFunc K) (p.comp (X^2)) := by
  simp [normalizedTupleTest,tupleRationalTest,RatFunc.smul_eq_C_mul,mul_assoc]

/-- The endpoint factor includes precisely the ratio of scalar normalizations. -/
theorem normalizedTupleTest_endpoint (s t : K) (hs : s≠0)
    (b : ℕ) (a : Fin 15 → ℕ) (i : Fin 15) (p : K[X]) :
    normalizedTupleTest t b (Function.update a i (a i+1))
      ((X-C (((a i+1:ℕ):K)^2))*p) = (t/s) • normalizedTupleTest s b a p := by
  rw [normalizedTupleTest_apply,tupleRationalTest_endpoint_step,
    normalizedTupleTest_apply,smul_smul,div_mul_cancel₀ _ hs]

def targetFactorialEndpoints : Fin 10 → ℕ := ![63,60,58,57,54,52,49,47,44,42]

/-- Exactly the factorial normalization N_n in the working manuscript. -/
def targetNormalization (n : ℕ) : K :=
  (∏ i : Fin 10, ((Nat.factorial (2*targetFactorialEndpoints i*n)):K)) /
    ((Nat.factorial (33*n):ℕ):K)^10

theorem targetNormalization_ne_zero (n : ℕ) : targetNormalization (K:=K) n≠0 := by
  apply div_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

def targetNormalizedWeight (n : ℕ) : RatFunc K :=
  RatFunc.C (targetNormalization n) * tupleWeight (100*n) (targetEndpointTuple n)

theorem targetNormalizedWeight_formula (n : ℕ) :
    targetNormalizedWeight (K:=K) n = RatFunc.C (targetNormalization n) *
      (algebraMap K[X] (RatFunc K) (C 2*X*(centeredDenominator (100*n))^5) /
        algebraMap K[X] (RatFunc K) (∏ i : Fin 15,centeredDenominator (targetEndpointTuple n i))) := rfl

def normalizedTargetFunctional (n : ℕ) (i : Fin 9) : K[X] →ₗ[K] K :=
  (nineRationalObservations (100*n) i).comp
    (normalizedTupleTest (targetNormalization n) (100*n) (targetEndpointTuple n))

theorem normalizedTargetFunctional_apply (n : ℕ) (i : Fin 9) (p : K[X]) :
    normalizedTargetFunctional (K:=K) n i p = targetNormalization n *
      observedTupleFunctional (nineRationalObservations (100*n)) (100*n) (targetEndpointTuple n) i p := by
  simp [normalizedTargetFunctional,normalizedTupleTest,observedTupleFunctional,smul_eq_mul]

/-- Independence also holds in the original Y=x² monomial coordinates. -/
theorem normalizedTargetNine_Y_independence (n : ℕ) (hn : 1≤n) :
    LinearIndependent K (fun i => initialMoments (normalizedTargetFunctional (K:=K) n i)) := by
  have h := (targetNine_independence (K:=K) n hn).units_smul
    (fun _ => Units.mk0 (targetNormalization (K:=K) n) (targetNormalization_ne_zero (K:=K) n))
  have heq : (fun i => initialMoments (normalizedTargetFunctional (K:=K) n i)) =
      (fun i => Units.mk0 (targetNormalization (K:=K) n) (targetNormalization_ne_zero (K:=K) n) •
        initialMoments (observedTupleFunctional (nineRationalObservations (K:=K) (100*n))
          (100*n) (targetEndpointTuple n) i)) := by
    funext i j
    change normalizedTargetFunctional n i (X^j.val)= _
    rw [normalizedTargetFunctional_apply]
    rfl
  rw [heq]
  exact h

def targetInitialMatrix (n : ℕ) : Matrix (Fin 9) (Fin 9) K :=
  fun i j => initialMoments (observedTupleFunctional (nineRationalObservations (100*n))
    (100*n) (targetEndpointTuple n) i) j

theorem targetInitialMatrix_isUnit (n : ℕ) (hn : 1≤n) :
    IsUnit (targetInitialMatrix (K:=K) n) :=
  Matrix.linearIndependent_rows_iff_isUnit.mp (targetNine_independence n hn)

/-- X=4Y: the j-th monomial in the manuscript coordinate is (4Y)^j. -/
def normalizedTargetMatrix (n : ℕ) : Matrix (Fin 9) (Fin 9) K :=
  fun i j => normalizedTargetFunctional n i ((C 4*X)^j.val)

theorem normalizedTargetMatrix_entry (n : ℕ) (i j : Fin 9) :
    normalizedTargetMatrix (K:=K) n i j =
      targetNormalization n * targetInitialMatrix n i j * (4:K)^j.val := by
  rw [normalizedTargetMatrix,normalizedTargetFunctional_apply,mul_pow,← map_pow,
    ← Polynomial.smul_eq_C_mul,map_smul]
  change targetNormalization n * ((4:K)^j.val * targetInitialMatrix n i j)= _
  ring

theorem normalizedTargetMatrix_factor (n : ℕ) :
    normalizedTargetMatrix (K:=K) n =
      Matrix.diagonal (fun _ : Fin 9 => targetNormalization n) * targetInitialMatrix n *
        Matrix.diagonal (fun j : Fin 9 => (4:K)^j.val) := by
  ext i j
  simp [normalizedTargetMatrix_entry,Matrix.diagonal_mul,Matrix.mul_diagonal]

theorem normalizedTargetMatrix_det (n : ℕ) :
    (normalizedTargetMatrix (K:=K) n).det =
      (targetNormalization n)^9 * (targetInitialMatrix n).det * (4:K)^36 := by
  rw [normalizedTargetMatrix_factor,Matrix.det_mul,Matrix.det_mul,Matrix.det_diagonal,
    Matrix.det_diagonal]
  congr 1
  · simp
  · norm_num [Fin.prod_univ_succ]

theorem normalizedTargetMatrix_det_ne_zero (n : ℕ) (hn : 1≤n) :
    (normalizedTargetMatrix (K:=K) n).det≠0 := by
  rw [normalizedTargetMatrix_det]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (targetNormalization_ne_zero n))
    ((Matrix.isUnit_iff_isUnit_det _).mp (targetInitialMatrix_isUnit n hn)).ne_zero)
    (pow_ne_zero _ (by norm_num))

/-- The concrete, factorial-normalized, X=4Y initial vectors are independent. -/
theorem normalizedTargetNine_independence (n : ℕ) (hn : 1≤n) :
    LinearIndependent K (fun i => fun j : Fin 9 =>
      normalizedTargetFunctional (K:=K) n i ((C 4*X)^j.val)) := by
  apply Matrix.linearIndependent_rows_iff_isUnit.mpr
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (normalizedTargetMatrix_det_ne_zero n hn).isUnit

theorem normalizedTargetNine_pearson (n : ℕ) (q : K[X])
    (hq : (q.natDegree:ℤ)+6≤361*(n:ℤ)) (i : Fin 9) :
    normalizedTargetFunctional n i
      ((pearsonOperator (pearsonPolynomial (n:K)) q).comp (C 4*X))=0 := by
  rw [normalizedTargetFunctional_apply,targetNine_pearson n q hq i,mul_zero]

/-- One assembled statement, with no assumed Pearson identity or seed determinant. -/
theorem normalizedTargetNine_assembled (n : ℕ) (hn : 1≤n) :
    LinearIndependent K (fun i => fun j : Fin 9 =>
      normalizedTargetFunctional (K:=K) n i ((C 4*X)^j.val)) ∧
    ∀ q : K[X], (q.natDegree:ℤ)+6≤361*(n:ℤ) → ∀ i : Fin 9,
      normalizedTargetFunctional n i
        ((pearsonOperator (pearsonPolynomial (n:K)) q).comp (C 4*X))=0 :=
  ⟨normalizedTargetNine_independence n hn,fun q hq i => normalizedTargetNine_pearson n q hq i⟩

theorem independent_rows_nonzero_coordinate (v : Fin 9 → Fin 9 → K)
    (hv : LinearIndependent K v) (c : Fin 9 → K) (hc : c 8≠0) :
    ∃ j : Fin 9, (∑ i : Fin 9,c i*v i j)≠0 := by
  by_contra h
  push_neg at h
  have hz : (∑ i : Fin 9,c i • v i)=0 := by
    funext j
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using h j
  exact hc ((Fintype.linearIndependent_iff.mp hv) c hz 8)

/-- A nonzero C_4 coefficient cannot be hidden by a relation among initial vectors. -/
theorem normalizedTarget_C4_exclusion (n : ℕ) (hn : 1≤n) (c : Fin 9 → K)
    (hc : c 8≠0) : ∃ j : Fin 9,
      (∑ i : Fin 9,c i * normalizedTargetFunctional (K:=K) n i ((C 4*X)^j.val))≠0 := by
  exact independent_rows_nonzero_coordinate _ (normalizedTargetNine_independence n hn) c hc

end OddZeta.FourValue

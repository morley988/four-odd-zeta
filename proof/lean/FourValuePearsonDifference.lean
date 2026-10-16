import FourValuePearsonConnection

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem rationalShift_comp_polynomial (t : K) (p f : K[X]) :
    rationalShift t (algebraMap K[X] (RatFunc K) (f.comp p)) =
      algebraMap K[X] (RatFunc K) (f.comp (p.taylor t)) := by
  rw [rationalShift_polynomial]
  simp only [Polynomial.taylor_apply,Polynomial.comp_assoc]

theorem tupleEvenWeight_physical_shift (b : ℕ) (a : Fin 15 → ℕ) :
    rationalShift (1:K) (tupleEvenWeight b a) *
      algebraMap K[X] (RatFunc K) ((tuplePearsonPolynomial b a).comp (-C 2*X-C 2)) =
      tupleEvenWeight b a *
        algebraMap K[X] (RatFunc K) ((tuplePearsonPolynomial b a).comp (C 2*X)) := by
  rw [tuplePearson_forward,tuplePearson_backward_shifted]
  simp only [map_mul,map_pow,Polynomial.C_ofNat,map_ofNat]
  linear_combination (2^20:RatFunc K)*tupleEvenWeight_shift (K:=K) b a

theorem tupleEvenWeight_physical_shift_back (b : ℕ) (a : Fin 15 → ℕ) :
    rationalShift (-1:K) (tupleEvenWeight b a) *
      algebraMap K[X] (RatFunc K) ((tuplePearsonPolynomial b a).comp (C 2*X-C 2)) =
      tupleEvenWeight b a *
        algebraMap K[X] (RatFunc K) ((tuplePearsonPolynomial b a).comp (-C 2*X)) := by
  have h := congrArg (rationalShift (-1:K)) (tupleEvenWeight_physical_shift (K:=K) b a)
  simp only [map_mul,rationalShift_add,neg_add_cancel,rationalShift_zero,
    rationalShift_comp_polynomial] at h
  have hp : (Polynomial.taylor (-1) (C 2*X) : K[X])=C 2*X-C 2 := by
    simp only [map_sub,map_neg,Polynomial.taylor_mul,Polynomial.taylor_C,Polynomial.taylor_X,map_one]
    ring
  have hm : (Polynomial.taylor (-1) (-C 2*X-C 2) : K[X])=-C 2*X := by
    simp only [map_sub,map_neg,Polynomial.taylor_mul,Polynomial.taylor_C,Polynomial.taylor_X,map_one]
    ring
  rw [hp,hm] at h
  exact h.symm

theorem pearsonBoundaryFunction_physical (b : ℕ) (a : Fin 15 → ℕ) (q : K[X])
    (ha : ∀ i,a i≤b) :
    pearsonBoundaryFunction b a q = tupleEvenWeight b a *
      algebraMap K[X] (RatFunc K) ((tuplePearsonPolynomial b a).comp (C 2*X)) *
      algebraMap K[X] (RatFunc K) (q.comp ((C 2*X+1)^2)) := by
  rw [pearsonBoundaryFunction_eq b a q ha,tuplePearson_forward]
  simp only [map_mul,map_pow,Polynomial.C_ofNat,map_ofNat]
  ring

theorem pearsonBoundaryFunction_shift_back (b : ℕ) (a : Fin 15 → ℕ) (q : K[X])
    (ha : ∀ i,a i≤b) :
    rationalShift (-1:K) (pearsonBoundaryFunction b a q) = tupleEvenWeight b a *
      algebraMap K[X] (RatFunc K) ((tuplePearsonPolynomial b a).comp (-C 2*X)) *
      algebraMap K[X] (RatFunc K) (q.comp ((C 2*X-1)^2)) := by
  rw [pearsonBoundaryFunction_physical b a q ha]
  simp only [map_mul,rationalShift_comp_polynomial]
  have hp : (Polynomial.taylor (-1) (C 2*X) : K[X])=C 2*X-C 2 := by
    simp only [map_sub,map_neg,Polynomial.taylor_mul,Polynomial.taylor_C,Polynomial.taylor_X,map_one]
    ring
  have hq : (Polynomial.taylor (-1) ((C 2*X+1)^2) : K[X])=(C 2*X-1)^2 := by
    simp only [Polynomial.taylor_pow,map_add,Polynomial.taylor_mul,Polynomial.taylor_C,
      Polynomial.taylor_X,Polynomial.taylor_one,map_neg,map_one]
    rw [map_ofNat]
    ring
  rw [hp,hq,tupleEvenWeight_physical_shift_back]

theorem pearsonOperator_scaled_reassembly (A q : K[X]) :
    (C 2*X)*(pearsonOperator A q).comp (C 4*X^2) =
      A.comp (C 2*X)*q.comp ((C 2*X+1)^2)-A.comp (-C 2*X)*q.comp ((C 2*X-1)^2) := by
  have h := congrArg (fun p : K[X] => p.comp (C 2*X)) (pearsonOperator_reassembly A q)
  simp only [Polynomial.mul_comp,Polynomial.expand_eq_comp_X_pow,Polynomial.comp_assoc,
    Polynomial.pow_comp,Polynomial.sub_comp,Polynomial.add_comp,Polynomial.neg_comp,
    Polynomial.C_comp,Polynomial.one_comp,Polynomial.X_comp] at h
  have hs : (C 2*X)^2=(C 4*X^2:K[X]) := by rw [map_ofNat,map_ofNat]; ring
  rw [hs,← neg_mul] at h
  exact h

/-- The actual rational Pearson relation is the half difference of the
proper boundary function. All coordinate rescalings are explicit. -/
theorem tupleRationalTest_pearson_difference (b : ℕ) (a : Fin 15 → ℕ) (q : K[X])
    (ha : ∀ i,a i≤b) :
    tupleRationalTest b a ((pearsonOperator (tuplePearsonPolynomial b a) q).comp (C 4*X)) =
      (2:K)⁻¹ • rationalDifference (pearsonBoundaryFunction b a q) := by
  rw [rationalDifference_apply,pearsonBoundaryFunction_shift_back b a q ha,
    pearsonBoundaryFunction_physical b a q ha]
  change tupleWeight b a * algebraMap K[X] (RatFunc K)
    (((pearsonOperator (tuplePearsonPolynomial b a) q).comp (C 4*X)).comp (X^2)) = _
  rw [tupleWeight_eq_X_even,Polynomial.comp_assoc]
  simp only [Polynomial.mul_comp,Polynomial.C_comp,Polynomial.X_comp]
  have h := congrArg (algebraMap K[X] (RatFunc K))
    (pearsonOperator_scaled_reassembly (tuplePearsonPolynomial (K:=K) b a) q)
  simp only [map_mul,map_sub,Polynomial.C_ofNat,map_ofNat,RatFunc.algebraMap_X] at h
  rw [RatFunc.smul_eq_C_mul,map_inv₀]
  norm_num only [RatFunc.C, map_ofNat]
  linear_combination (tupleEvenWeight (K:=K) b a)/2*h

end OddZeta.FourValue

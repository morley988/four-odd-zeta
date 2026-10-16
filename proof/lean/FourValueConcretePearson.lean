import FourValuePearsonDifference
import FourValueFamilyIndependence

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- The actual sum of order-k principal-part coefficients of W(x)P(x²). -/
def concreteB (b : ℕ) (a : Fin 15 → ℕ) (k : ℕ) : K[X] →ₗ[K] K :=
  (rationalB b k).comp (tupleRationalTest b a)

/-- The finite harmonic coefficient functional, with common boundary b+1. -/
def concreteC (b : ℕ) (a : Fin 15 → ℕ) (h : ℕ) : K[X] →ₗ[K] K :=
  (rationalC b h).comp (tupleRationalTest b a)

/-- Unconditional concrete B Pearson identity. -/
theorem concreteB_pearson (b : ℕ) (a : Fin 15 → ℕ) (ha : ∀ i,a i≤b)
    (q : K[X]) (hq : (q.natDegree:ℤ)+6≤tupleBeta b a) (k : ℕ) (hk : 0<k) :
    concreteB b a k ((pearsonOperator (tuplePearsonPolynomial b a) q).comp (C 4*X))=0 := by
  obtain ⟨c,hc⟩ := pearsonBoundary_partialFractions b a q ha hq
  change rationalB b k (tupleRationalTest b a _)=0
  rw [tupleRationalTest_pearson_difference b a q ha,map_smul,
    rationalB_difference_of_partialFractions b k hk _ c hc,smul_zero]

/-- Unconditional concrete C Pearson identity for the five Taylor orders. -/
theorem concreteC_pearson (b : ℕ) (a : Fin 15 → ℕ) (ha : ∀ i,a i≤b)
    (q : K[X]) (hq : (q.natDegree:ℤ)+6≤tupleBeta b a) (h : ℕ) (hh : h<5) :
    concreteC b a h ((pearsonOperator (tuplePearsonPolynomial b a) q).comp (C 4*X))=0 := by
  obtain ⟨c,hc⟩ := pearsonBoundary_partialFractions b a q ha hq
  change rationalC b h (tupleRationalTest b a _)=0
  rw [tupleRationalTest_pearson_difference b a q ha,map_smul,
    rationalC_difference_of_partialFractions b h _ c hc,
    pearsonBoundary_coeff_zero b a q h hh,neg_zero,smul_zero]

theorem nineRationalObservations_pearson (b : ℕ) (a : Fin 15 → ℕ)
    (ha : ∀ i,a i≤b) (q : K[X]) (hq : (q.natDegree:ℤ)+6≤tupleBeta b a) (j : Fin 9) :
    observedTupleFunctional (nineRationalObservations (K:=K) b) b a j
      ((pearsonOperator (tuplePearsonPolynomial b a) q).comp (C 4*X))=0 := by
  have hB := concreteB_pearson b a ha q hq
  have hC := concreteC_pearson b a ha q hq
  fin_cases j
  · exact hB 3 (by norm_num)
  · exact hB 5 (by norm_num)
  · exact hB 7 (by norm_num)
  · exact hB 9 (by norm_num)
  · exact hC 0 (by norm_num)
  · exact hC 1 (by norm_num)
  · exact hC 2 (by norm_num)
  · exact hC 3 (by norm_num)
  · exact hC 4 (by norm_num)

theorem nineRationalObservations_relation (b : ℕ) (a : Fin 15 → ℕ)
    (ha : ∀ i,a i≤b) (hbeta : 6≤tupleBeta b a) (j : Fin 9) :
    observedTupleFunctional (nineRationalObservations (K:=K) b) b a j (tupleMomentRelation b a)=0 := by
  exact nineRationalObservations_pearson (K:=K) b a ha 1 (by simpa using hbeta) j

/-- The Pearson hypotheses of the endpoint theorem are discharged for the
actual nine observations. Only the actual seed independence remains. -/
theorem concreteNine_independence_of_seed (b : ℕ) (hb : 6≤b)
    (hseed : LinearIndependent K (fun j => initialMoments
      (observedTupleFunctional (nineRationalObservations (K:=K) b) b (seedTuple b) j)))
    (a : Fin 15 → ℕ) (ha : ∀ i,a i≤b) (hbeta : 6≤tupleBeta b a) :
    LinearIndependent K (fun j => initialMoments
      (observedTupleFunctional (nineRationalObservations (K:=K) b) b a j)) := by
  apply observedTuple_independence_of_seed _ b hb _ hseed a ha hbeta
  intro a ha hbeta j
  exact nineRationalObservations_relation b a ha hbeta j

end OddZeta.FourValue

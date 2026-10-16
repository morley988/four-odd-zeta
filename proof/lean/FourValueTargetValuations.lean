import FourValueLaurentValuations

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {p : ℕ} [Fact p.Prime]

def centeredResidueCount (p : ℕ) (a : ℤ) (b : ℕ) : ℤ :=
  ∑ t ∈ poleWindow b, rootResidueWeight p (a-t)

def targetLocalWeight (p n : ℕ) (a : ℤ) : ℤ :=
  targetNormalizationFloor p n + rootResidueWeight p a +
    5*centeredResidueCount p a (100*n) -
      ∑ i : Fin 15, centeredResidueCount p a (targetEndpointTuple n i)

theorem LaurentPadicLower.mono {a : ℚ} {u v : ℤ} {f : RatFunc ℚ}
    (hf : LaurentPadicLower p a v f) (h : u≤v) : LaurentPadicLower p a u f := by
  intro j
  exact (hf j).mono (by omega)

theorem centeredDenominator_laurentPadicLower (a : ℤ) (b : ℕ) :
    LaurentPadicLower p (a:ℚ) (centeredResidueCount p a b)
      (algebraMap ℚ[X] (RatFunc ℚ) (centeredDenominator b)) := by
  rw [centeredDenominator_integerProduct]
  simpa only [integerRootProduct, map_prod, centeredResidueCount] using
    LaurentPadicLower.prod (p:=p) (poleWindow b) (a:ℚ)
      (fun t => rootResidueWeight p (a-t))
      (fun t => algebraMap ℚ[X] (RatFunc ℚ) (X-C (t:ℚ)))
      (fun t ht => linearFactor_laurentPadicLower a t)

theorem inverseCenteredDenominator_laurentPadicLower (a : ℤ) (b : ℕ)
    (hs : ∀ t ∈ poleWindow b, (a-t).natAbs<p^2) :
    LaurentPadicLower p (a:ℚ) (-centeredResidueCount p a b)
      ((algebraMap ℚ[X] (RatFunc ℚ) (centeredDenominator b))⁻¹) := by
  rw [centeredDenominator_integerProduct]
  simpa only [integerRootProduct, map_prod, centeredResidueCount, Finset.sum_neg_distrib,
    rationalPole, pow_one, map_sub, Finset.prod_inv_distrib] using
    LaurentPadicLower.prod (p:=p) (poleWindow b) (a:ℚ)
      (fun t => -rootResidueWeight p (a-t)) (fun t => rationalPole (t:ℚ) 1)
      (fun t ht => inverseLinearFactor_laurentPadicLower a t (hs t ht))

theorem target_root_difference_lt_square (n : ℕ) (a : ℤ) (ha : a ∈ poleWindow (100*n))
    (hs : 800*n<p^2) (i : Fin 15) (t : ℤ) (ht : t∈poleWindow (targetEndpointTuple n i)) :
    (a-t).natAbs<p^2 := by
  have hi := targetEndpointTuple_le_67 n i
  simp only [poleWindow, Finset.mem_Icc] at ha ht
  have hcast : (800:ℤ)*n<(p:ℤ)^2 := by exact_mod_cast hs
  have hic : (targetEndpointTuple n i:ℤ) ≤ 67*n := by exact_mod_cast hi
  have he : -((p:ℤ)^2)<a-t ∧ a-t<(p:ℤ)^2 := by push_cast at ha; omega
  have hab : |a-t| < (p:ℤ)^2 := abs_lt.mpr he
  rw [← Int.natCast_natAbs] at hab
  exact_mod_cast hab

/-- The actual normalized rational weight satisfies the local coefficient
bound at every integer in the pole window, including the central class. -/
theorem targetNormalizedWeight_laurentPadicLower (n : ℕ) (a : ℤ)
    (ha : a ∈ poleWindow (100*n)) (hs : 800*n<p^2) :
    LaurentPadicLower p (a:ℚ) (targetLocalWeight p n a)
      (targetNormalizedWeight (K:=ℚ) n) := by
  have hN : LaurentPadicLower p (a:ℚ) (targetNormalizationFloor p n)
      (RatFunc.C (targetNormalization (K:=ℚ) n)) :=
    LaurentPadicLower.constant (Or.inr (le_of_eq (targetNormalization_padicVal_large n hs).symm))
  have h2 := LaurentPadicLower.constant (a:=(a:ℚ)) (PadicLower.natCast (p:=p) 2)
  have hx := linearFactor_laurentPadicLower (p:=p) a 0
  simp only [sub_zero, Int.cast_zero, map_zero] at hx
  have hD := (centeredDenominator_laurentPadicLower (p:=p) a (100*n)).pow 5
  have hQ := LaurentPadicLower.prod (p:=p) Finset.univ (a:ℚ)
    (fun i : Fin 15 => -centeredResidueCount p a (targetEndpointTuple n i))
    (fun i => (algebraMap ℚ[X] (RatFunc ℚ) (centeredDenominator (targetEndpointTuple n i)))⁻¹)
    (fun i hi => inverseCenteredDenominator_laurentPadicLower a _
      (fun t ht => target_root_difference_lt_square n a ha hs i t ht))
  have h := hN.mul (((h2.mul hx).mul hD).mul hQ)
  convert h using 1 <;> try rfl
  · simp [targetLocalWeight, Finset.sum_neg_distrib]
    ring
  · simp [targetNormalizedWeight, tupleWeight, tupleNumerator, tupleDenominator,
      div_eq_mul_inv, Finset.prod_inv_distrib, mul_assoc]

/-- Coefficients of the actual weight at Laurent order -k. -/
theorem targetNormalizedWeight_coefficient_padicLower (n : ℕ) (a : ℤ)
    (ha : a ∈ poleWindow (100*n)) (hs : 800*n<p^2) (k : ℕ) :
    PadicLower p (targetLocalWeight p n a + k)
      (rationalCoefficientAt (a:ℚ) (-(k:ℤ)) (targetNormalizedWeight (K:=ℚ) n)) := by
  simpa using targetNormalizedWeight_laurentPadicLower n a ha hs (-(k:ℤ))
end OddZeta.FourValue

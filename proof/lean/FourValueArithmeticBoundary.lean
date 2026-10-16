import FourValueArithmeticAssembly

noncomputable section
namespace OddZeta.FourValue
open Polynomial

theorem targetZetaTest_coefficient_outside (n : ℕ) (P : ℂ[X]) (a : ℤ)
    (ha : a∉poleWindow (67*n)) (k : ℕ) (hk : 0<k) :
    rationalCoefficientAt (a:ℂ) (-(k:ℤ)) (targetZetaTest n P)=0 := by
  have hq : (tupleDenominator (K:=ℂ) (targetEndpointTuple n)).eval (a:ℂ) ≠ 0 := by
    simp only [tupleDenominator, Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi hz
    obtain ⟨j,hj,hj',he⟩ := (centeredDenominator_eval_zero_iff _ _).mp hz
    have haj : a=j := by exact_mod_cast he
    apply ha
    have hib := targetEndpointTuple_le_67 n i
    simp only [poleWindow,Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  rw [targetZetaTest, map_smul, tupleRationalTest_fraction,
    rationalCoefficientAt_regular_neg _ _ _ hq _ (by omega), smul_zero]

theorem targetZetaTest_partialFractions_67 (n : ℕ) (P : ℂ[X]) (hP : P.natDegree≤361*n+3) :
    ∃ c : ℤ → Fin 10 → ℂ, targetZetaTest n P =
      ∑ a ∈ poleWindow (67*n), ∑ k : Fin 10, c a k • rationalPole (a:ℂ) (k.val+1) := by
  obtain ⟨c,hc⟩ := targetZetaTest_partialFractions n P hP
  refine ⟨c, hc.trans ?_⟩
  symm
  apply Finset.sum_subset
  · intro a ha
    simp only [poleWindow,Finset.mem_Icc] at ha ⊢
    omega
  · intro a ha ha'
    apply Finset.sum_eq_zero
    intro k hk
    have he := integer_partialFractions_coefficient (poleWindow (100*n)) 10 c
      (targetZetaTest n P) hc a ha k
    rw [targetZetaTest_coefficient_outside n P a ha' (k.val+1) (by omega)] at he
    rw [← he, zero_smul]

theorem targetZetaTest_B_boundary (n k : ℕ) (hk : 0<k) (P : ℂ[X]) :
    rationalB (67*n) k (targetZetaTest n P) = rationalB (100*n) k (targetZetaTest n P) := by
  simp only [rationalB, LinearMap.sum_apply]
  apply Finset.sum_subset
  · intro a ha
    simp only [poleWindow,Finset.mem_Icc] at ha ⊢
    omega
  · intro a ha ha'
    exact targetZetaTest_coefficient_outside n P a ha' k hk

theorem targetZetaTest_C4_boundary (n : ℕ) (P : ℂ[X]) (hP : P.natDegree≤361*n+3) :
    rationalC (67*n) 4 (targetZetaTest n P) = rationalC (100*n) 4 (targetZetaTest n P) := by
  obtain ⟨c,hc⟩ := targetZetaTest_partialFractions_67 n P hP
  have h := (hasSum_rationalZetaForm (67*n) 4 (by decide) (targetZetaTest n P) c hc).unique
    (classicalZetaFunctional_hasSum n P hP)
  rw [← targetZetaTest_zetaForm n P hP] at h
  simp only [rationalZetaForm, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply] at h
  have he : (∑ k ∈ Finset.range 10,
      ((-1:ℂ)^4*(Nat.choose (k+4) 4:ℂ)*riemannZeta ((k+4+1:ℕ):ℂ)) •
        rationalB (67*n) (k+1) (targetZetaTest n P)) =
      ∑ k ∈ Finset.range 10,
      ((-1:ℂ)^4*(Nat.choose (k+4) 4:ℂ)*riemannZeta ((k+4+1:ℕ):ℂ)) •
        rationalB (100*n) (k+1) (targetZetaTest n P) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [targetZetaTest_B_boundary n (k+1) (by omega)]
  rw [he] at h
  exact add_right_cancel h

theorem rationalPhysicalTest_eq_smul (n : ℕ) (P : ℚ[X]) :
    rationalPhysicalTest n P = targetNormalization (K:=ℚ) n •
      tupleRationalTest (100*n) (targetEndpointTuple n) (P.comp (C 4*X)) := by
  simp [rationalPhysicalTest, targetNormalizedWeight, tupleRationalTest,
    RatFunc.smul_eq_C_mul, mul_assoc]

theorem rationalPhysicalTest_cast (n : ℕ) (P : ℚ[X]) :
    coefficientRatFuncMap (algebraMap ℚ ℂ) (rationalPhysicalTest n P) =
      targetZetaTest n (P.map (algebraMap ℚ ℂ)) := by
  rw [rationalPhysicalTest_eq_smul, RatFunc.smul_eq_C_mul, map_mul,
    coefficientRatFuncMap_C, targetNormalization_map, tupleRationalTest_map]
  unfold targetZetaTest
  rw [RatFunc.smul_eq_C_mul]
  congr 2
  rw [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
  norm_num

theorem rationalPhysicalTest_C4_boundary (n : ℕ) (P : ℚ[X]) (hP : P.natDegree≤361*n+3) :
    rationalC (67*n) 4 (rationalPhysicalTest n P) = rationalC (100*n) 4 (rationalPhysicalTest n P) := by
  apply (algebraMap ℚ ℂ).injective
  rw [← rationalC_map, ← rationalC_map, rationalPhysicalTest_cast]
  exact targetZetaTest_C4_boundary n _ ((Polynomial.natDegree_map_le).trans hP)

theorem rationalPhysicalTest_B_boundary (n k : ℕ) (hk : 0<k) (P : ℚ[X]) :
    rationalB (67*n) k (rationalPhysicalTest n P) = rationalB (100*n) k (rationalPhysicalTest n P) := by
  apply (algebraMap ℚ ℂ).injective
  rw [← rationalB_map, ← rationalB_map, rationalPhysicalTest_cast]
  exact targetZetaTest_B_boundary n k hk _

/-- The exact rational pencil decomposes at the manuscript boundary 67n. -/
theorem rationalFourValueFunctional_local_sum_67 (n : ℕ) (lambda : Fin 4 → ℚ)
    (P : ℚ[X]) (hP : P.natDegree≤361*n+3) :
    rationalFourValueFunctional n lambda P =
      ∑ a ∈ poleWindow (67*n), localFourValueObservation (67*n) a lambda (rationalPhysicalTest n P) := by
  have he (b : ℕ) : (∑ a ∈ poleWindow b, localFourValueObservation b a lambda (rationalPhysicalTest n P)) =
      rationalC b 4 (rationalPhysicalTest n P) +
      lambda 0*rationalB b 3 (rationalPhysicalTest n P) +
      lambda 1*rationalB b 5 (rationalPhysicalTest n P) +
      lambda 2*rationalB b 7 (rationalPhysicalTest n P) +
      lambda 3*rationalB b 9 (rationalPhysicalTest n P) := by
    simp [localFourValueObservation,localFourthObservation,rationalC,rationalB,
      Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_neg_distrib,smul_eq_mul,mul_assoc]
    norm_num [show ∀ k : ℕ, k+4+1=k+5 by omega]
  rw [rationalFourValueFunctional_local_sum, he, he, rationalPhysicalTest_C4_boundary n P hP]
  rw [rationalPhysicalTest_B_boundary n 3 (by decide), rationalPhysicalTest_B_boundary n 5 (by decide),
    rationalPhysicalTest_B_boundary n 7 (by decide), rationalPhysicalTest_B_boundary n 9 (by decide)]
end OddZeta.FourValue

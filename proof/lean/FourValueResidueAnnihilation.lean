import FourValueResidueCapacity
import FourValueListRootFactors
import FourValueAnnihilatorRank

noncomputable section
namespace OddZeta.FourValue
open Polynomial
open scoped RatFunc
variable {p : ℕ} [Fact p.Prime]

theorem physical_square_factor_dvd (P : ℚ[X]) (a : ℤ) (m : ℕ)
    (h : (X-C (4*(a:ℚ)^2))^m∣P) :
    (X-C (a:ℚ))^m ∣ ((P.comp (C 4*X)).comp (X^2)) := by
  obtain ⟨Q,rfl⟩ := h
  simp only [mul_comp,pow_comp,sub_comp,X_comp,C_comp]
  have he : C (4:ℚ)*X^2-C (4*(a:ℚ)^2)=C 4*(X-C (a:ℚ))*(X+C (a:ℚ)) := by
    simp only [map_mul,map_pow]
    ring
  rw [he,mul_pow,mul_pow]
  refine ⟨C 4^m*(X+C (a:ℚ))^m*((Q.comp (C 4*X)).comp (X^2)),?_⟩
  ring

theorem targetResidueAnnihilator_divisibility (n : ℕ) (r a : ℤ)
    (ha : (p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) :
    (X-C (a:ℚ))^((targetPoleList n).count a) ∣
      (((targetResidueAnnihilator p n r).comp (C 4*X)).comp (X^2)) := by
  apply physical_square_factor_dvd
  rcases ha with ha | ha
  · have hh : (p:ℤ)∣r-a := by simpa using dvd_neg.mpr ha
    have hf := linearRootProduct_list_factor
      ((targetPoleList n).filter (fun t => (p:ℤ)∣r-t)) (fun t : ℤ => 4*(t:ℚ)^2) a
    rw [List.count_filter (by simpa using hh)] at hf
    exact ⟨_,hf⟩
  · have hh : (p:ℤ)∣r-(-a) := by simpa [sub_neg_eq_add,add_comm] using ha
    have hf := linearRootProduct_list_factor
      ((targetPoleList n).filter (fun t => (p:ℤ)∣r-t)) (fun t : ℤ => 4*(t:ℚ)^2) (-a)
    rw [List.count_filter (by simpa using hh),targetPoleList_count_neg] at hf
    simp only [Int.cast_neg,neg_sq] at hf
    exact ⟨_,hf⟩

theorem rationalPhysicalTest_divisible_regular (n : ℕ) (a : ℤ) (P Q : ℚ[X])
    (hP : (X-C (a:ℚ))^((targetPoleList n).count a) ∣ ((P.comp (C 4*X)).comp (X^2)))
    (j : ℤ) (hj : j<0) :
    rationalCoefficientAt (a:ℚ) j (rationalPhysicalTest n (P*Q))=0 := by
  obtain ⟨U,hU⟩ := hP
  let D := linearRootProduct (((targetPoleList n).filter (fun t => t≠a)).map (fun t : ℤ => (t:ℚ)))
  have hD : D.eval (a:ℚ)≠0 := integerListRoot_remainder_regular _ a
  have hfactor : targetReducedDenominator (K:=ℚ) n=(X-C (a:ℚ))^((targetPoleList n).count a)*D := by
    rw [targetReducedDenominator_list]
    exact linearRootProduct_list_factor _ _ a
  have hpow : algebraMap ℚ[X] (RatFunc ℚ) ((X-C (a:ℚ))^((targetPoleList n).count a))≠0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero _ (monic_X_sub_C (a:ℚ)).ne_zero)
  have he : rationalPhysicalTest n (P*Q)=
      algebraMap ℚ[X] (RatFunc ℚ)
        (C (targetNormalization n)*(C 2*X*targetGapPolynomial n^5)*U*((Q.comp (C 4*X)).comp (X^2))) /
      algebraMap ℚ[X] (RatFunc ℚ) D := by
    rw [rationalPhysicalTest,targetNormalizedWeight_cancelled,hfactor]
    simp only [mul_comp,hU,map_mul]
    rw [RatFunc.algebraMap_C]
    field_simp
    simp only [RatFunc.algebraMap_C]
    ring
  rw [he]
  exact rationalCoefficientAt_regular_neg _ _ _ hD j hj

theorem residuePolynomialFunctional_annihilator (n b : ℕ) (S : Finset ℤ) (r : ℤ)
    (lambda : Fin 4 → ℚ) (hS : ∀ a∈S,(p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) (Q : ℚ[X]) :
    residuePolynomialFunctional n b S lambda (targetResidueAnnihilator p n r*Q)=0 := by
  rw [residuePolynomialFunctional_apply]
  apply Finset.sum_eq_zero
  intro a ha
  have hc (j : ℤ) (hj : j<0) := rationalPhysicalTest_divisible_regular n a
    (targetResidueAnnihilator p n r) Q (targetResidueAnnihilator_divisibility n r a (hS a ha)) j hj
  unfold localFourValueObservation localFourthObservation
  simp only [hc (-3) (by omega),hc (-5) (by omega),hc (-7) (by omega),hc (-9) (by omega),mul_zero,add_zero]
  rw [Finset.sum_eq_zero]
  · simp
  · intro k hk
    simp only [hc (-((k+1:ℕ):ℤ)) (by omega),mul_zero]

theorem selectedResidueMatrix_rank_capacity (n b : ℕ) (S : Finset ℤ) (r : ℤ)
    (lambda : Fin 4 → ℚ) {k : ℕ} (rows cols : Fin k → Fin (targetHankelDegree n+1))
    (hS : ∀ a∈S,(p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) :
    (selectedResidueMatrix n b S lambda rows cols).rank≤targetResidueCapacity p n r := by
  rw [← targetResidueAnnihilator_degree n r]
  exact polynomialGram_rank_le_annihilator _ _ _ _ (targetResidueAnnihilator_monic n r)
    (residuePolynomialFunctional_annihilator n b S r lambda hS)

theorem selectedResidueMatrix_det_zero_capacity (n b : ℕ) (S : Finset ℤ) (r : ℤ)
    (lambda : Fin 4 → ℚ) {k : ℕ} (rows cols : Fin k → Fin (targetHankelDegree n+1))
    (hS : ∀ a∈S,(p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) (hk : targetResidueCapacity p n r<k) :
    (selectedResidueMatrix n b S lambda rows cols).det=0 := by
  apply polynomialGram_det_zero_of_capacity _ _ _ _ (targetResidueAnnihilator_monic n r)
    (residuePolynomialFunctional_annihilator n b S r lambda hS)
  simpa [targetResidueAnnihilator_degree] using hk
end OddZeta.FourValue

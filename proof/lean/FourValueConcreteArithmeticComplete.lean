import FourValueResidueAnnihilation
import FourValueSmallPrimeEntries

noncomputable section
namespace OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

theorem selectedResidueMatrix_allPrime_bound (n b : ℕ) (S : Finset ℤ) (lambda : Fin 4 → ℚ)
    {k : ℕ} (rows cols : Fin k → Fin (targetHankelDegree n+1))
    (hS : ∀ a∈S,a∈poleWindow (100*n) ∧ (b-a).toNat≤800*n) :
    PadicLower p ((k:ℤ)*(-40*(Nat.log p (800*n):ℤ)-
      (padicValNat p (rationalPencilDenominator lambda):ℤ)))
      (selectedResidueMatrix n b S lambda rows cols).det := by
  have h := padicLower_det_weighted (p:=p) (selectedResidueMatrix n b S lambda rows cols)
    (fun _ => 0) (fun _ => 0) _ (fun i j => by
      change PadicLower p _ (residuePolynomialFunctional n b S lambda
        (squareBasisPolynomial (rows i).val*squareBasisPolynomial (cols j).val))
      rw [residuePolynomialFunctional_apply]
      apply padicLower_sum
      intro a ha
      simpa using squareBasis_local_allPrime_bound (p:=p) n b (rows i) (cols j) a lambda (hS a ha).1 (hS a ha).2)
  simpa using h

/-- The exceptional central class is finite and has an explicit capacity;
no nonzero-residue or odd-prime hypothesis is used here. -/
theorem targetResidueCapacity_zero (n : ℕ) :
    (targetResidueCapacity p n 0:ℤ)=
      2*(∑ i : Fin 10,((targetFactorialEndpoints i*n/p:ℕ):ℤ))+10 := by
  rw [targetResidueCapacity_floor]
  simp only [add_zero,sub_zero,Int.natCast_ediv,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  ring

/-- The same independently selected rational minor used by the exact zeta
series identity satisfies the all-prime bound. -/
theorem classicalZetaSeries_nonzero_minor_allPrime (n : ℕ) (hn : 1≤n) (z : Fin 4 → ℚ)
    (hz : ∀ i : Fin 4,riemannZeta ((![7,9,11,13] : Fin 4 → ℂ) i)=(z i:ℂ)) :
    ∃ (rows cols : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1)) (q : ℚ),
      q≠0 ∧ ((classicalZetaSeriesMatrix n).submatrix rows cols).det=(q:ℂ) ∧
      ∀ p : ℕ,∀ hp : p.Prime,
        letI : Fact p.Prime := ⟨hp⟩
        ((targetHankelDegree n+1-4:ℕ):ℤ)*(-40*(Nat.log p (800*n):ℤ)-
          (padicValNat p (rationalPencilDenominator (fun i => (![15,70,210,495] : Fin 4 → ℚ) i*z i)):ℤ))
          ≤padicValRat p q := by
  let lambda : Fin 4 → ℚ := fun i => (![15,70,210,495] : Fin 4 → ℚ) i*z i
  obtain ⟨rows,cols,hq⟩ := rationalFourValueMatrix_nonzero_minor n hn lambda
  refine ⟨rows,cols,((rationalFourValueMatrix n lambda).submatrix rows cols).det,hq,?_,?_⟩
  · rw [classicalZetaSeriesMatrix_rational n z hz]
    change (((rationalFourValueMatrix n lambda).submatrix rows cols).map (algebraMap ℚ ℂ)).det=_
    convert ((algebraMap ℚ ℂ).map_det ((rationalFourValueMatrix n lambda).submatrix rows cols)).symm using 1 <;> rfl
  · intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    exact (rationalFourValueMatrix_allPrime_minor n lambda rows cols).of_ne_zero hq

/-- Exact finite residue allocation before the subsequent global optimization.
Any finite labelling partitions the actual selected matrix without changing
its rows or columns. -/
theorem rationalFourValueMatrix_selected_partition (n : ℕ) (lambda : Fin 4 → ℚ) {k d : ℕ}
    (rows cols : Fin k → Fin (targetHankelDegree n+1)) (label : ℤ → Fin d) :
    (rationalFourValueMatrix n lambda).submatrix rows cols =
      ∑ r : Fin d,selectedResidueMatrix n (67*n)
        ((poleWindow (67*n)).filter (fun a => label a=r)) lambda rows cols := by
  rw [rationalFourValueMatrix_selected_boundary]
  ext i j
  simp only [Matrix.sum_apply,selectedResidueMatrix,polynomialGram,residuePolynomialFunctional_apply]
  exact (Finset.sum_fiberwise (poleWindow (67*n)) label
    (fun a => localFourValueObservation (67*n) a lambda
      (rationalPhysicalTest n (squareBasisPolynomial (rows i).val*squareBasisPolynomial (cols j).val)))).symm
end OddZeta.FourValue

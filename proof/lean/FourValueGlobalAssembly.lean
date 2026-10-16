import FourValueGlobalPartition

noncomputable section
namespace OddZeta.FourValue.Corrected
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem residueClassMatrix_zero_partition (n b d : ℕ) (lambda : Fin 4 → ℚ) :
 (residueClassMatrix n b (poleWindow (63*n)) 0 lambda Fin.val Fin.val : Matrix (Fin d) (Fin d) ℚ) =
 ∑ r : Fin (p/2+1),integralLocalMatrix n b (pairedPoles n r) lambda d := by
 ext i j
 simp only [Matrix.sum_apply, integralLocalMatrix, polynomialGram,
   residuePolynomialFunctional_apply, pairedPoles, residueClassMatrix, translatedAnalyticMonomial]
 simp only [Int.cast_zero,zero_pow (by omega : 2≠0),map_zero,sub_zero,← pow_add]
 exact (sum_fiberwise (poleWindow (63*n)) (pairedLabel (p:=p)) (fun a => localFourValueObservation b a lambda (rationalAnalyticTest n ((X : ℚ[X])^(i.val+j.val))))).symm

/-- The factorial normalization is paid once, after assembly of all residue classes. -/
theorem rationalFourValueMatrix_dual_bound (n : ℕ) (lambda : Fin 4 → ℚ) {k : ℕ}
 (rows cols : Fin k → Fin (targetHankelDegree n+1)) (price : ℤ)
 (pen : Fin (p/2+1) → ℤ)
 (hlocal : ∀ r, Allocation.MinorLower (p:=p)
   (integralLocalMatrix n (67*n) (pairedPoles n r) lambda (targetHankelDegree n+1))
   (fun m => price*m-pen r)) :
 PadicLower p (price*k-∑r,pen r-selectedFactorialCost p n rows cols)
   ((rationalFourValueMatrix n lambda).submatrix rows cols).det := by
 have he : (rationalFourValueMatrix n lambda).submatrix rows cols =
   selectedResidueMatrix n (67*n) (poleWindow (63*n)) lambda rows cols := by
   ext i j
   change rationalFourValueFunctional n lambda
     (squareBasisPolynomial (rows i).val*squareBasisPolynomial (cols j).val)=_
   rw [rationalFourValueFunctional_local_sum_63]
   · exact (residuePolynomialFunctional_apply _ _ _ _ _).symm
   · have h := Polynomial.natDegree_mul_le (p:=squareBasisPolynomial (K:=ℚ) (rows i).val)
       (q:=squareBasisPolynomial (cols j).val)
     rw [squareBasisPolynomial_degree,squareBasisPolynomial_degree] at h
     have hr := (rows i).isLt
     have hc := (cols j).isLt
     unfold targetHankelDegree at hr hc
     omega
 rw [he]
 apply selectedResidueMatrix_transfer n (67*n) (poleWindow (63*n)) 0 lambda rows cols
 intro u v
 rw [residueClassMatrix_zero_partition (p:=p)]
 have heq : (∑ r : Fin (p/2+1),integralLocalMatrix n (67*n) (pairedPoles n r) lambda
     (targetHankelDegree n+1)).submatrix u v =
     ∑ r : Fin (p/2+1),(integralLocalMatrix n (67*n) (pairedPoles n r) lambda
       (targetHankelDegree n+1)).submatrix u v := by
   ext i j
   simp [Matrix.sum_apply, Matrix.submatrix_apply]
 rw [heq]
 apply Allocation.sum_matrix_dual_lower _ price pen
 intro r m a b
 simpa only [Matrix.submatrix_submatrix] using hlocal r m (u ∘ a) (v ∘ b)

#print axioms rationalFourValueMatrix_dual_bound
end OddZeta.FourValue.Corrected

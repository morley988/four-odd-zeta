import FourValueAllocationBlocks
import FourValueCorrectedZeta

noncomputable section
namespace OddZeta.FourValue.Corrected
open Polynomial
set_option maxHeartbeats 200000
attribute [-instance] DivisionRing.toRatAlgebra
variable {p : ℕ} [Fact p.Prime]

/-- Local moment matrices in an integral monomial basis. -/
def integralLocalMatrix (n b : ℕ) (S : Finset ℤ) (lambda : Fin 4 → ℚ) (d : ℕ) :
 Matrix (Fin d) (Fin d) ℚ :=
 polynomialGram (residuePolynomialFunctional n b S lambda)
   (fun i => X^i.val) (fun j => X^j.val)

theorem monomial_integral (i : ℕ) : PolynomialPadicLower p 0 (X^i : ℚ[X]) := by
 have h : PolynomialPadicLower p 0 (X : ℚ[X]) := by
   simpa using integerLinearFactor_polynomialPadicLower (p:=p) 0
 simpa using h.pow i

theorem integralLocalMatrix_transfer (n b : ℕ) (S : Finset ℤ) (r : ℤ)
 (lambda : Fin 4 → ℚ) {k d : ℕ} (rows cols : Fin k → Fin d) (w : ℤ)
 (hM : ∀ u v : Fin k → Fin d,
   PadicLower p w ((residueClassMatrix n b S r lambda Fin.val Fin.val).submatrix u v).det) :
 PadicLower p w ((integralLocalMatrix n b S lambda d).submatrix rows cols).det := by
 change PadicLower p w (polynomialGram (residuePolynomialFunctional n b S lambda)
   (fun i => X^(rows i).val) (fun j => X^(cols j).val)).det
 rw [polynomialGram_translated (d:=d) _ _ _ ((r:ℚ)^2)
   (fun i => by simpa using (rows i).isLt) (fun j => by simpa using (cols j).isLt)]
 have he : (fun (l h : Fin d) => residuePolynomialFunctional n b S lambda
     ((X-C ((r:ℚ)^2))^(l.val+h.val))) = residueClassMatrix n b S r lambda Fin.val Fin.val := by
   ext i j
   exact residuePolynomialFunctional_apply _ _ _ _ _
 rw [he]
 apply padicLower_det_integral_change _ _ _ w hM
 · intro i j
   have ht := (monomial_integral (p:=p) (rows i).val).taylor (r^2) j.val
   change PadicLower p 0 (((X^(rows i).val : ℚ[X]).taylor ((r^2:ℤ):ℚ)).coeff j.val) at ht
   rw [Int.cast_pow] at ht
   exact ht
 · intro i j
   have ht := (monomial_integral (p:=p) (cols j).val).taylor (r^2) i.val
   change PadicLower p 0 (((X^(cols j).val : ℚ[X]).taylor ((r^2:ℤ):ℚ)).coeff i.val) at ht
   rw [Int.cast_pow] at ht
   exact ht

theorem integralLocalMatrix_capacity (n b : ℕ) (S : Finset ℤ) (r : ℤ)
 (lambda : Fin 4 → ℚ) {k d : ℕ} (rows cols : Fin k → Fin d)
 (hS : ∀ a∈S,(p:ℤ)∣a-r ∨ (p:ℤ)∣a+r)
 (hk : targetResidueCapacity p n r<k) :
 ((integralLocalMatrix n b S lambda d).submatrix rows cols).det=0 := by
 apply polynomialGram_det_zero_of_capacity _ _ _ _ (targetResidueAnnihilator_monic n r)
   (residuePolynomialFunctional_annihilator n b S r lambda hS)
 simpa [targetResidueAnnihilator_degree] using hk

theorem integralLocalMatrix_bad (n b : ℕ) (S : Finset ℤ) (r : ℤ)
 (lambda : Fin 4 → ℚ) {k d : ℕ} (rows cols : Fin k → Fin d)
 (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda)
 (hS : ∀ a∈S,a∈poleWindow (100*n) ∧ ((p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) ∧ (b-a).toNat<p^2) :
 PadicLower p ((k:ℤ)^2+(targetLocalWeight p n r-5)*k)
   ((integralLocalMatrix n b S lambda d).submatrix rows cols).det := by
 apply integralLocalMatrix_transfer n b S r lambda rows cols
 intro u v
 by_cases hu : Function.Injective u
 · by_cases hv : Function.Injective v
   · exact pairedResidueClassMatrix_det_padicLower n b S r lambda
       (fun i => (u i).val) (fun j => (v j).val)
       (Fin.val_injective.comp hu) (Fin.val_injective.comp hv) hs hp hS
   · rw [matrix_submatrix_det_zero_of_not_injective _ _ _ (Or.inr hv)]
     exact PadicLower.zero _
 · rw [matrix_submatrix_det_zero_of_not_injective _ _ _ (Or.inl hu)]
   exact PadicLower.zero _

theorem integralLocalMatrix_good (n b : ℕ) (S : Finset ℤ) (r : ℤ)
 (lambda : Fin 4 → ℚ) {k d : ℕ} (rows cols : Fin k → Fin d)
 (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda)
 (hS : ∀ a∈S,a∈poleWindow (100*n) ∧ ((p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) ∧ (b-a).toNat<p) :
 PadicLower p ((k:ℤ)^2+targetLocalWeight p n r*k)
   ((integralLocalMatrix n b S lambda d).submatrix rows cols).det := by
 apply integralLocalMatrix_transfer n b S r lambda rows cols
 intro u v
 by_cases hu : Function.Injective u
 · by_cases hv : Function.Injective v
   · exact pairedResidueClassMatrix_det_padicLower_good n b S r lambda
       (fun i => (u i).val) (fun j => (v j).val)
       (Fin.val_injective.comp hu) (Fin.val_injective.comp hv) hs hp hS
   · rw [matrix_submatrix_det_zero_of_not_injective _ _ _ (Or.inr hv)]
     exact PadicLower.zero _
 · rw [matrix_submatrix_det_zero_of_not_injective _ _ _ (Or.inl hu)]
   exact PadicLower.zero _

theorem integralLocalMatrix_single (n b : ℕ) (S : Finset ℤ) (r : ℤ)
 (lambda : Fin 4 → ℚ) {k d : ℕ} (rows cols : Fin k → Fin d)
 (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda)
 (hS : ∀ a∈S,a∈poleWindow (63*n) ∧ centeredResidueCount p a (63*n)=1 ∧
   ((p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) ∧ (b-a).toNat<p) :
 PadicLower p (max ((k:ℤ)^2+targetLocalWeight p n r*k) ((k:ℤ)*targetNormalizationFloor p n))
   ((integralLocalMatrix n b S lambda d).submatrix rows cols).det := by
 apply integralLocalMatrix_transfer n b S r lambda rows cols
 intro u v
 by_cases hu : Function.Injective u
 · by_cases hv : Function.Injective v
   · exact singleNode_residueMatrix_det_max n b S r lambda
       (fun i => (u i).val) (fun j => (v j).val)
       (Fin.val_injective.comp hu) (Fin.val_injective.comp hv) hs hp hS
   · rw [matrix_submatrix_det_zero_of_not_injective _ _ _ (Or.inr hv)]
     exact PadicLower.zero _
 · rw [matrix_submatrix_det_zero_of_not_injective _ _ _ (Or.inl hu)]
   exact PadicLower.zero _

/-- Finite capacity and finite local costs imply a dual minor bound. -/
theorem minorLower_of_capacity {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ)
 (cap : ℕ) (cost : ℕ → ℤ) (price : ℤ) (hzero : cost 0=0)
 (hc : ∀ m,cap<m → ∀ rows cols : Fin m → Fin d,(A.submatrix rows cols).det=0)
 (hb : ∀ m,m≤cap → ∀ rows cols : Fin m → Fin d,PadicLower p (cost m) (A.submatrix rows cols).det) :
 Allocation.MinorLower (p:=p) A (fun m => price*m-Allocation.penalty cap cost price) := by
 intro m rows cols
 by_cases hm : m≤cap
 · exact (hb m hm rows cols).mono (Allocation.cost_dual_lower cap m cost price hzero hm)
 · exact Or.inl (hc m (by omega) rows cols)

end OddZeta.FourValue.Corrected
attribute [instance] DivisionRing.toRatAlgebra

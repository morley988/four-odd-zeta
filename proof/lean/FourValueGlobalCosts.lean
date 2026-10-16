import FourValueGlobalAssembly

noncomputable section
namespace OddZeta.FourValue.Corrected
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]

/-- Exact admissibility tests on the surviving poles, including the central class. -/
def goodClass (n : ℕ) (r : Fin (p/2+1)) : Prop :=
 ∀ a∈pairedPoles n r, ((67*n:ℕ)-a).toNat<p

def singleClass (n : ℕ) (r : Fin (p/2+1)) : Prop :=
 ∀ a∈pairedPoles n r, centeredResidueCount p a (63*n)=1

instance (n : ℕ) (r : Fin (p/2+1)) : Decidable (goodClass n r) := Classical.propDecidable _
instance (n : ℕ) (r : Fin (p/2+1)) : Decidable (singleClass n r) := Classical.propDecidable _

def classCost (n : ℕ) (r : Fin (p/2+1)) : ℕ → ℤ :=
 if goodClass n r then
   if singleClass n r then Allocation.singleCost (targetLocalWeight p n r.val) (targetNormalizationFloor p n)
   else Allocation.quadraticCost (targetLocalWeight p n r.val)
 else Allocation.quadraticCost (targetLocalWeight p n r.val-5)

theorem classCost_zero (n : ℕ) (r : Fin (p/2+1)) : classCost n r 0=0 := by
 unfold classCost
 split_ifs <;> simp [Allocation.singleCost,Allocation.quadraticCost]

theorem pairedPoles_small (n : ℕ) (r : Fin (p/2+1)) (hs : 800*n<p^2)
 (a : ℤ) (ha : a∈pairedPoles n r) :
 a∈poleWindow (100*n) ∧ ((p:ℤ)∣a-r.val ∨ (p:ℤ)∣a+r.val) ∧ ((67*n:ℕ)-a).toNat<p^2 := by
 obtain ⟨haw,har⟩ := mem_pairedPoles n r a ha
 refine ⟨?_,har,?_⟩
 · simp only [poleWindow,mem_Icc] at haw ⊢
   omega
 · simp only [poleWindow,mem_Icc] at haw
   omega

theorem integralLocalMatrix_class_bound (n : ℕ) (lambda : Fin 4 → ℚ)
 (r : Fin (p/2+1)) {k d : ℕ} (rows cols : Fin k → Fin d)
 (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda) :
 PadicLower p (classCost n r k)
   ((integralLocalMatrix n (67*n) (pairedPoles n r) lambda d).submatrix rows cols).det := by
 unfold classCost
 split_ifs with hg ht
 · simpa only [Allocation.singleCost,Allocation.quadraticCost,mul_comm] using
     integralLocalMatrix_single n (67*n) (pairedPoles n r) r.val lambda rows cols hs hp
       (fun a ha => ⟨(mem_pairedPoles n r a ha).1, ht a ha,
         (mem_pairedPoles n r a ha).2,hg a ha⟩)
 · exact integralLocalMatrix_good n (67*n) (pairedPoles n r) r.val lambda rows cols hs hp
     (fun a ha => ⟨(pairedPoles_small n r hs a ha).1,(mem_pairedPoles n r a ha).2,hg a ha⟩)
 · exact integralLocalMatrix_bad n (67*n) (pairedPoles n r) r.val lambda rows cols hs hp
     (pairedPoles_small n r hs)

/-- An unconditional finite dual valuation bound for the actual corrected determinant. -/
theorem rationalFourValueMatrix_finite_dual (n : ℕ) (lambda : Fin 4 → ℚ) {k : ℕ}
 (rows cols : Fin k → Fin (targetHankelDegree n+1)) (price : ℤ)
 (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda) :
 PadicLower p (price*k-
   ∑r : Fin (p/2+1),Allocation.penalty (targetResidueCapacity p n r.val) (classCost n r) price
   -selectedFactorialCost p n rows cols)
   ((rationalFourValueMatrix n lambda).submatrix rows cols).det := by
 apply rationalFourValueMatrix_dual_bound n lambda rows cols price
 intro r
 apply minorLower_of_capacity _ _ _ _ (classCost_zero n r)
 · intro m hm u v
   exact integralLocalMatrix_capacity n (67*n) (pairedPoles n r) r.val lambda u v
     (fun a ha => (mem_pairedPoles n r a ha).2) hm
 · intro m hm u v
   exact integralLocalMatrix_class_bound n lambda r u v hs hp

#print axioms rationalFourValueMatrix_finite_dual
end OddZeta.FourValue.Corrected

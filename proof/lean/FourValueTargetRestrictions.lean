import FourValueGridCIdentity
import FourValueResidueKernel
import FourValueNormalization
import FourValueFiniteDimension

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def targetPhysicalRow (n : ℕ) (i : Fin 9) : Fin 9 → K :=
  fun j => observedTupleFunctional (nineRationalObservations (100*n))
    (100*n) (targetEndpointTuple n) i ((C 4*X)^j.val)

theorem targetPhysicalRow_independent (n : ℕ) (hn : 1≤n) :
    LinearIndependent K (targetPhysicalRow (K:=K) n) := by
  have hv := (normalizedTargetNine_independence (K:=K) n hn).units_smul
    (fun _ => Units.mk0 (targetNormalization (K:=K) n)⁻¹ (inv_ne_zero (targetNormalization_ne_zero n)))
  convert hv using 1
  funext i j
  simp [targetPhysicalRow,normalizedTargetFunctional_apply,Units.smul_def,smul_eq_mul,
    targetNormalization_ne_zero,mul_assoc]

def restrictionRowIndex : Fin 6 → Fin 9 := ![0,1,2,3,5,7]
def restrictionLaurentOrder : Fin 6 → ℤ := ![-3,-5,-7,-9,1,3]
def restrictionScale : Fin 6 → K := ![2,2,2,2,-4,-4]

theorem restrictionRowIndex_injective : Function.Injective restrictionRowIndex := by
  decide

theorem restrictionScale_ne_zero (i : Fin 6) : restrictionScale (K:=K) i≠0 := by
  fin_cases i <;> norm_num [restrictionScale]

theorem target_initial_degree_range (n : ℕ) (hn : 1≤n) (j : Fin 9) :
    (((X^j.val : K[X]).comp (C 4*X)).natDegree:ℤ) ≤
      tupleBeta (100*n) (targetEndpointTuple n)+3 := by
  rw [targetEndpointTuple_beta]
  have hd := Polynomial.natDegree_comp_le (p:=(X^j.val:K[X])) (q:=C 4*X)
  have h4 : (C 4*X:K[X]).natDegree=1 := by
    rw [Polynomial.natDegree_C_mul (by norm_num : (4:K)≠0),Polynomial.natDegree_X]
  rw [Polynomial.natDegree_X_pow,h4,mul_one] at hd
  have hj := j.isLt
  omega

theorem targetGrid_minus_one_restriction (n : ℕ) (hn : 1≤n) :
    liftedInitialMoments (finiteGridFunctional (K:=K) (100*n) (targetEndpointTuple n) (-1))=0 := by
  funext j
  change finiteGridFunctional _ _ (-1) (X*expand K 2 (X^j.val))=0
  rw [Polynomial.expand_eq_comp_X_pow,
    show (-1:ℤ)=-(1:ℕ) by norm_num,finiteGridFunctional_negative_lift,
    concreteB_one_zero _ _ (targetEndpointTuple_bounded n) _ (target_initial_degree_range n hn j),mul_zero]

theorem targetGrid_six_restrictions (n : ℕ) (hn : 1≤n) (i : Fin 6) :
    liftedInitialMoments (finiteGridFunctional (K:=K) (100*n) (targetEndpointTuple n)
      (restrictionLaurentOrder i)) = restrictionScale (K:=K) i • targetPhysicalRow (K:=K) n (restrictionRowIndex i) := by
  funext j
  change finiteGridFunctional _ _ _ (X*expand K 2 (X^j.val)) = _
  rw [Polynomial.expand_eq_comp_X_pow]
  have hB (k : ℕ) := finiteGridFunctional_negative_lift (K:=K)
    (100*n) k (targetEndpointTuple n) (X^j.val)
  have hC (h : ℕ) (hh : Odd h) := finiteGridFunctional_positive_lift (K:=K)
    (100*n) h (targetEndpointTuple n) (targetEndpointTuple_bounded n) hh
    (X^j.val) (target_initial_degree_range n hn j)
  simp only [Polynomial.pow_comp,Polynomial.X_comp] at hB hC ⊢
  fin_cases i
  · exact (hB 3).trans (by rfl)
  · exact (hB 5).trans (by rfl)
  · exact (hB 7).trans (by rfl)
  · exact (hB 9).trans (by rfl)
  · exact (hC 1 (by decide)).trans (by rfl)
  · exact (hC 3 (by decide)).trans (by rfl)

/-- The actual restriction map, in the physical X=4Y coordinate. -/
def finitePearsonRestriction (n : ℕ) :
    finitePearsonSpace (pearsonPolynomial (n:ℂ)) →ₗ[ℂ] (Fin 9 → ℂ) where
  toFun U := liftedInitialMoments U.val
  map_add' U V := by ext j; rfl
  map_smul' c U := by ext j; rfl

def targetFiniteGrid (n : ℕ) (h : ℤ) (hh : h<5) :
    finitePearsonSpace (pearsonPolynomial (n:ℂ)) :=
  ⟨finiteGridFunctional (100*n) (targetEndpointTuple n) h,by
    rw [← targetEndpointTuple_pearson]
    exact finiteGridFunctional_isFinitePearson _ _ (targetEndpointTuple_bounded n) h hh⟩

theorem target_six_in_restriction_range (n : ℕ) (hn : 1≤n) (i : Fin 6) :
    targetPhysicalRow (K:=ℂ) n (restrictionRowIndex i) ∈ (finitePearsonRestriction n).range := by
  have hh : restrictionLaurentOrder i<5 := by fin_cases i <;> norm_num [restrictionLaurentOrder]
  refine ⟨(restrictionScale (K:=ℂ) i)⁻¹ • targetFiniteGrid n (restrictionLaurentOrder i) hh,?_⟩
  rw [map_smul]
  change (restrictionScale i)⁻¹ • liftedInitialMoments
    (finiteGridFunctional (100*n) (targetEndpointTuple n) (restrictionLaurentOrder i)) = _
  rw [targetGrid_six_restrictions n hn i,smul_smul,inv_mul_cancel₀ (restrictionScale_ne_zero i),one_smul]

theorem target_restriction_kernel_nonzero (n : ℕ) (hn : 1≤n) :
    ∃ U ∈ (finitePearsonRestriction n).ker, U≠0 := by
  refine ⟨targetFiniteGrid n (-1) (by omega),?_,?_⟩
  · exact targetGrid_minus_one_restriction n hn
  · intro hz
    exact targetGrid_minus_one_ne_zero (K:=ℂ) n (congrArg Subtype.val hz)

end OddZeta.FourValue

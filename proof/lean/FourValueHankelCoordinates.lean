import FourValueHankelKernel
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K]

def polynomialFromVector (m : ℕ) : (Fin (m+1) → K) →ₗ[K] K[X] :=
  (Polynomial.degreeLT K (m+1)).subtype.comp
    (Polynomial.degreeLTEquiv K (m+1)).symm.toLinearMap

theorem polynomialFromVector_coeff (m : ℕ) (c : Fin (m+1) → K) (i : Fin (m+1)) :
    (polynomialFromVector m c).coeff i.val=c i := by
  exact congrFun ((Polynomial.degreeLTEquiv K (m+1)).apply_symm_apply c) i

theorem polynomialFromVector_degree (m : ℕ) (c : Fin (m+1) → K) :
    (polynomialFromVector m c).natDegree≤m := by
  have h := ((Polynomial.degreeLTEquiv K (m+1)).symm c).property
  have hd : (polynomialFromVector m c).degree < m+1 := Polynomial.mem_degreeLT.mp h
  by_cases hz : polynomialFromVector m c=0
  · simp [hz]
  · have hn : (polynomialFromVector m c).natDegree<m+1 :=
      (Polynomial.natDegree_lt_iff_degree_lt hz).mpr (by simpa using hd)
    omega

theorem polynomialFromVector_of_coeffs (m : ℕ) (q : K[X]) (hq : q.natDegree≤m) :
    polynomialFromVector m (fun i => q.coeff i.val)=q := by
  have hmem : q ∈ Polynomial.degreeLT K (m+1) := by
    rw [Polynomial.degreeLT_succ_eq_degreeLE,Polynomial.mem_degreeLE]
    exact Polynomial.natDegree_le_iff_degree_le.mp hq
  exact congrArg (fun z : Polynomial.degreeLT K (m+1) => z.val)
    ((Polynomial.degreeLTEquiv K (m+1)).symm_apply_apply ⟨q,hmem⟩)

theorem hankel_mulVec_polynomialFromVector (L : K[X] →ₗ[K] K) (m : ℕ)
    (c : Fin (m+1) → K) (j : Fin (m+1)) :
    (momentHankel L m).mulVec c j = L (polynomialFromVector m c * X^j.val) := by
  change (∑ i, L (X^(j.val+i.val))*c i)=
    L ((∑ i : Fin (m+1), Polynomial.monomial i.val (c i))*X^j.val)
  rw [Finset.sum_mul,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Polynomial.C_mul_X_pow_eq_monomial,mul_assoc,← pow_add,
    ← Polynomial.smul_eq_C_mul,map_smul]
  simp [smul_eq_mul,add_comm,mul_comm]

theorem hankel_mulVec_coeffs (L : K[X] →ₗ[K] K) (m : ℕ)
    (q : K[X]) (hq : q.natDegree≤m) (j : Fin (m+1)) :
    (momentHankel L m).mulVec (fun i => q.coeff i.val) j=L (q*X^j.val) := by
  rw [hankel_mulVec_polynomialFromVector,polynomialFromVector_of_coeffs m q hq]

theorem degreeLT_natDegree_lt {b : ℕ} (hb : 0<b) (q : Polynomial.degreeLT K b) :
    q.val.natDegree<b := by
  by_cases hz : q.val=0
  · simpa [hz] using hb
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr (Polynomial.mem_degreeLT.mp q.property)

theorem degreeLT_finrank (b : ℕ) : Module.finrank K (Polynomial.degreeLT K b)=b := by
  have h := (Polynomial.degreeLTEquiv K b).finrank_eq
  simpa using h

end OddZeta.FourValue

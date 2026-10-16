import FourValueRankAssembly
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

/-! The elementary first half of the truncated Hankel annihilator theorem.
The longer range `j <= 2*m-r` is NOT asserted here. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K]

/-- Rank at most `r` produces a nonzero polynomial of degree at most `r`
annihilating the original matrix rows `0,...,m`. This does not yet give the
extra recurrence relations needed for the full apolar lemma. -/
theorem hankel_kernel_polynomial (L : K[X] →ₗ[K] K) (m r : ℕ) (hr : r≤m)
    (hrank : (momentHankel L m).rank≤r) :
    ∃ p : K[X], p≠0 ∧ p.natDegree≤r ∧ ∀ j≤m, L (p*X^j)=0 := by
  classical
  let A := momentHankel L m
  let S := Submodule.span K (Set.range A.col)
  let idx (i : Fin (r+1)) : Fin (m+1) := ⟨i.val,by omega⟩
  let v (i : Fin (r+1)) : S := ⟨A.col (idx i),Submodule.subset_span ⟨idx i,rfl⟩⟩
  have hdep : ¬LinearIndependent K v := by
    intro hi
    have h := hi.fintype_card_le_finrank
    have hdim : Module.finrank K S≤r := by
      change Module.finrank K (Submodule.span K (Set.range A.col))≤r
      rw [← Matrix.rank_eq_finrank_span_cols]
      exact hrank
    simp only [Fintype.card_fin] at h
    omega
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨c,hc,i,hi⟩ := hdep
  let p : K[X] := ∑ k : Fin (r+1), c k • X^k.val
  have hcoeff (k : Fin (r+1)) : p.coeff k.val=c k := by
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_smul, Polynomial.coeff_X_pow,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
    have heq (j : Fin (r+1)) : k.val=j.val ↔ j=k := by
      constructor
      · intro h
        exact Fin.ext h.symm
      · rintro rfl
        rfl
    simp_rw [heq]
    simp
  have hp : p≠0 := by
    intro hz
    apply hi
    rw [← hcoeff i,hz,Polynomial.coeff_zero]
  refine ⟨p,hp,?_,?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k _
    exact (Polynomial.natDegree_smul_le (c k) (X^k.val)).trans (by simp; omega)
  · intro j hj
    have h := congrArg (fun z : S => (z : Fin (m+1) → K) ⟨j,by omega⟩) hc
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      Submodule.coe_zero, Pi.zero_apply, v, A, Matrix.col, Matrix.transpose_apply, momentHankel, idx,
      smul_eq_mul] at h
    change L ((∑ k : Fin (r+1), c k • X^k.val)*X^j)=0
    rw [Finset.sum_mul,map_sum]
    simpa only [smul_mul_assoc,map_smul,smul_eq_mul,← pow_add,add_comm] using h

/-- Normalization to a monic kernel polynomial does not lose degree or the
matrix-row relations. -/
theorem hankel_monic_kernel_polynomial (L : K[X] →ₗ[K] K) (m r : ℕ) (hr : r≤m)
    (hrank : (momentHankel L m).rank≤r) :
    ∃ p : K[X], p.Monic ∧ p.natDegree≤r ∧ ∀ j≤m, L (p*X^j)=0 := by
  obtain ⟨p,hp,hdeg,hann⟩ := hankel_kernel_polynomial L m r hr hrank
  have hlc : p.leadingCoeff≠0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  refine ⟨C (p.leadingCoeff⁻¹)*p,
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc),?_,?_⟩
  · rw [← Polynomial.smul_eq_C_mul]
    exact (Polynomial.natDegree_smul_le _ p).trans hdeg
  · intro j hj
    rw [mul_assoc,← Polynomial.smul_eq_C_mul,map_smul,hann j hj,smul_zero]

/-- A least-degree monic matrix-row annihilator exists. -/
theorem hankel_minimal_monic_kernel (L : K[X] →ₗ[K] K) (m r : ℕ) (hr : r≤m)
    (hrank : (momentHankel L m).rank≤r) :
    ∃ p : K[X], p.Monic ∧ p.natDegree≤r ∧
      (∀ j≤m, L (p*X^j)=0) ∧
      (∀ q : K[X], q.Monic → (∀ j≤m, L (q*X^j)=0) → p.natDegree≤q.natDegree) := by
  classical
  obtain ⟨q,hq,hqdeg,hqann⟩ := hankel_monic_kernel_polynomial L m r hr hrank
  have hex : ∃ d : ℕ, ∃ p : K[X], p.Monic ∧ p.natDegree=d ∧ ∀ j≤m, L (p*X^j)=0 :=
    ⟨q.natDegree,q,hq,rfl,hqann⟩
  obtain ⟨p,hp,hpdeg,hpann⟩ := Nat.find_spec hex
  have hmin (f : K[X]) (hf : f.Monic) (hann : ∀ j≤m, L (f*X^j)=0) :
      p.natDegree≤f.natDegree := by
    rw [hpdeg]
    exact Nat.find_min' hex ⟨f,hf,rfl,hann⟩
  exact ⟨p,hp,(hmin q hq hqann).trans hqdeg,hpann,hmin⟩

/-- Relations in the leading block propagate across the original rows
whenever a monic kernel polynomial of that size is available. -/
theorem leading_kernel_relation_propagates (L : K[X] →ₗ[K] K) (m : ℕ)
    (p : K[X]) (hp : p.Monic) (hsize : p.natDegree≤m+1)
    (hpann : ∀ j≤m, L (p*X^j)=0) (q : K[X]) (hq : q.natDegree<p.natDegree)
    (hinit : ∀ j<p.natDegree, L (q*X^j)=0) :
    ∀ j≤m, L (q*X^j)=0 := by
  let E := recurrenceExtension L p
  have hE : ∀ f : K[X], E (p*f)=0 := recurrenceExtension_annihilates L hp
  have hi : ∀ j<p.natDegree, E (q*X^j)=0 := by
    intro j hj
    rw [recurrenceExtension_agrees L hp m hpann]
    · exact hinit j hj
    · have hd := Polynomial.natDegree_mul_le (p:=q) (q:=X^j)
      simp only [Polynomial.natDegree_X_pow] at hd
      omega
  have hall := annihilator_propagates_tests E hp hE q X hi
  intro j hj
  have hagree : E (q*X^j)=L (q*X^j) := by
    apply recurrenceExtension_agrees L hp m hpann
    have hd := Polynomial.natDegree_mul_le (p:=q) (q:=X^j)
    simp only [Polynomial.natDegree_X_pow] at hd
    omega
  rw [← hagree]
  exact hall j

/-- Minimality makes the leading moment pairing nondegenerate. This is the
first structural step toward treating the possible root at infinity. -/
theorem minimal_kernel_leading_nondegenerate (L : K[X] →ₗ[K] K) (m : ℕ)
    (p : K[X]) (hp : p.Monic) (hsize : p.natDegree≤m+1)
    (hpann : ∀ j≤m, L (p*X^j)=0)
    (hmin : ∀ f : K[X], f.Monic → (∀ j≤m, L (f*X^j)=0) → p.natDegree≤f.natDegree)
    (q : K[X]) (hq : q.natDegree<p.natDegree)
    (hinit : ∀ j<p.natDegree, L (q*X^j)=0) : q=0 := by
  by_contra hq0
  have hann := leading_kernel_relation_propagates L m p hp hsize hpann q hq hinit
  have hlc : q.leadingCoeff≠0 := Polynomial.leadingCoeff_ne_zero.mpr hq0
  let f := C (q.leadingCoeff⁻¹)*q
  have hf : f.Monic := Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    (inv_mul_cancel₀ hlc)
  have hfann : ∀ j≤m, L (f*X^j)=0 := by
    intro j hj
    dsimp [f]
    rw [mul_assoc,← Polynomial.smul_eq_C_mul,map_smul,hann j hj,smul_zero]
  have hfd : f.natDegree≤q.natDegree := by
    dsimp [f]
    rw [← Polynomial.smul_eq_C_mul]
    exact Polynomial.natDegree_smul_le _ q
  have h := hmin f hf hfann
  omega

end OddZeta.FourValue

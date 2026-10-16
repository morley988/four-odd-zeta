import FourValueHankelDivisibility
import FourValueHankelCoordinates
import Mathlib.Tactic

/-! An elementary dimension proof of the full truncated Hankel annihilator
range, including degree loss corresponding to roots at infinity. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K]

/-- A failed relation in the required range would make the matrix kernel
too small. This is the dimension argument behind the short annihilator. -/
theorem hankel_first_failure_impossible (L : K[X] →ₗ[K] K) (m r t : ℕ)
    (hr : r≤m) (hrank : (momentHankel L m).rank≤r)
    (p : K[X]) (hp : p.Monic) (hpdeg : p.natDegree≤r)
    (hpann : ∀ j≤m, L (p*X^j)=0)
    (hmin : ∀ f : K[X], f.Monic → (∀ j≤m, L (f*X^j)=0) → p.natDegree≤f.natDegree)
    (ht : m<t) (htop : t≤2*m-r)
    (hzero : ∀ j<t, L (p*X^j)=0) (hfail : L (p*X^t)≠0) : False := by
  let D := Polynomial.degreeLT K (t-m)
  let H := (momentHankel L m).mulVecLin
  letI : FiniteDimensional K D := FiniteDimensional.of_injective
    (Polynomial.degreeLTEquiv K (t-m)).toLinearMap (Polynomial.degreeLTEquiv K (t-m)).injective
  have hproddeg (q : D) : (p*q.val).natDegree≤m := by
    have hqd := degreeLT_natDegree_lt (K:=K) (by omega : 0<t-m) q
    have hmul := Polynomial.natDegree_mul_le (p:=p) (q:=q.val)
    omega
  have hann (q : D) : (fun i : Fin (m+1) => (p*q.val).coeff i.val) ∈ H.ker := by
    apply LinearMap.mem_ker.mpr
    funext j
    change (momentHankel L m).mulVec (fun i => (p*q.val).coeff i.val) j=0
    rw [hankel_mulVec_coeffs L m _ (hproddeg q),mul_assoc]
    apply recurrence_relations_span L p (t-1) (fun k hk => hzero k (by omega))
    have hqd := degreeLT_natDegree_lt (K:=K) (by omega : 0<t-m) q
    have hmul := Polynomial.natDegree_mul_le (p:=q.val) (q:=X^j.val)
    simp only [Polynomial.natDegree_X_pow] at hmul
    have := j.isLt
    omega
  let T : D →ₗ[K] H.ker := {
    toFun := fun q => ⟨fun i => (p*q.val).coeff i.val,hann q⟩
    map_add' := by
      intro q q'
      apply Subtype.ext
      funext i
      simp [mul_add]
    map_smul' := by
      intro c q
      apply Subtype.ext
      funext i
      simp [mul_smul_comm] }
  have hsurj : Function.Surjective T := by
    intro c
    let q := polynomialFromVector m c.val
    have hqdeg : q.natDegree≤m := polynomialFromVector_degree m c.val
    have hqann : ∀ j≤m, L (q*X^j)=0 := by
      intro j hj
      have h := congrFun (LinearMap.mem_ker.mp c.property) (⟨j,by omega⟩ : Fin (m+1))
      change (momentHankel L m).mulVec c.val ⟨j,by omega⟩=0 at h
      rwa [hankel_mulVec_polynomialFromVector] at h
    obtain ⟨a,ha⟩ := minimal_kernel_divides L m p hp (by omega) hpann hmin q hqdeg hqann
    have haD : a ∈ D := by
      apply Polynomial.mem_degreeLT.mpr
      by_cases ha0 : a=0
      · simp [ha0]
      · apply (Polynomial.natDegree_lt_iff_degree_lt ha0).mp
        apply kernel_quotient_degree_bound L m t p a hp.ne_zero ha0
        · rwa [← ha]
        · exact ht
        · exact hzero
        · exact hfail
        · intro j hj
          rw [← ha]
          exact hqann j hj
    refine ⟨⟨a,haD⟩,?_⟩
    apply Subtype.ext
    funext i
    change (p*a).coeff i.val=c.val i
    rw [← ha]
    exact polynomialFromVector_coeff m c.val i
  have hdim : Module.finrank K H.ker≤t-m := by
    have h := LinearMap.finrank_le_finrank_of_surjective hsurj
    simpa only [D,degreeLT_finrank] using h
  have hnull : (momentHankel L m).rank + Module.finrank K H.ker=m+1 := by
    simpa [H,Matrix.rank] using LinearMap.finrank_range_add_finrank_ker H
  omega

/-- The full short-annihilator conclusion follows from rank, without
assuming a flat extension or a nonzero leading principal minor. -/
theorem hankel_short_annihilator (L : K[X] →ₗ[K] K) (m r : ℕ) (hr : r≤m)
    (hrank : (momentHankel L m).rank≤r) : HasShortAnnihilator L m r := by
  classical
  obtain ⟨p,hp,hpdeg,hpann,hmin⟩ := hankel_minimal_monic_kernel L m r hr hrank
  refine ⟨p,hp,hpdeg,?_⟩
  intro j hj
  by_contra hfailj
  have hex : ∃ t : ℕ, L (p*X^t)≠0 := ⟨j,hfailj⟩
  let t := Nat.find hex
  have htj : t≤j := Nat.find_min' hex hfailj
  have hfail : L (p*X^t)≠0 := Nat.find_spec hex
  have hzero : ∀ k<t, L (p*X^k)=0 := by
    intro k hk
    exact not_not.mp (Nat.find_min hex hk)
  have ht : m<t := by
    by_contra h
    exact hfail (hpann t (by omega))
  exact hankel_first_failure_impossible L m r t hr hrank p hp hpdeg hpann hmin
    ht (by omega) hzero hfail

/-- The rank assembly no longer needs apolarity as an external hypothesis.
The family-specific initial-vector exclusion is still an explicit input. -/
theorem hankel_rank_bound_of_finite_exclusion [CharZero K] (L : K[X] →ₗ[K] K) (A : K[X]) (m : ℕ)
    (hA : A.natDegree≤20)
    (hrel : ∀ j : ℕ, j+9≤2*m → L (pearsonOperator A (X^j))=0)
    (hexclusion : ∀ U : K[X] →ₗ[K] K, IsFinitePearson A U →
      liftedInitialMoments U≠initialMoments L) :
    m+1-4≤(momentHankel L m).rank :=
  hankel_rank_bound_of_short_annihilators L A m hA hrel
    (fun r hr hRank => hankel_short_annihilator L m r hr hRank) hexclusion

end OddZeta.FourValue

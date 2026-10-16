import FourValueHankelKernel
import FourValueJetFamilies
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

/-! Divisibility of all matrix-row kernel polynomials by a least-degree
kernel polynomial, and a bound from the first failed recurrence relation. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K]

/-- Every polynomial in the original Hankel kernel is divisible by a
least-degree monic kernel polynomial. -/
theorem minimal_kernel_divides (L : K[X] →ₗ[K] K) (m : ℕ)
    (p : K[X]) (hp : p.Monic) (hsize : p.natDegree≤m+1)
    (hpann : ∀ j≤m, L (p*X^j)=0)
    (hmin : ∀ f : K[X], f.Monic → (∀ j≤m, L (f*X^j)=0) → p.natDegree≤f.natDegree)
    (q : K[X]) (hq : q.natDegree≤m) (hqann : ∀ j≤m, L (q*X^j)=0) : p∣q := by
  by_cases hp1 : p=1
  · simp [hp1]
  apply (Polynomial.modByMonic_eq_zero_iff_dvd hp).mp
  apply minimal_kernel_leading_nondegenerate L m p hp hsize hpann hmin
    (q %ₘ p) (Polynomial.natDegree_modByMonic_lt q hp hp1)
  intro j hj
  have hdivdeg : ((q /ₘ p)*X^j).natDegree≤m := by
    have h := Polynomial.natDegree_mul_le (p:=q /ₘ p) (q:=X^j)
    rw [Polynomial.natDegree_divByMonic q hp, Polynomial.natDegree_X_pow] at h
    omega
  have hzero := recurrence_relations_span L p m hpann ((q /ₘ p)*X^j) hdivdeg
  have heq := congrArg (fun f : K[X] => L (f*X^j)) (Polynomial.modByMonic_add_div q p)
  rw [add_mul,map_add,mul_assoc,hzero,add_zero,hqann j (by omega)] at heq
  exact heq

/-- Pairing with the first nonzero moment detects the leading coefficient.
This supplies the degree bound on a quotient kernel polynomial. -/
theorem first_nonzero_moment_detects_top (F : K[X] →ₗ[K] K) (t : ℕ)
    (hzero : ∀ k<t, F (X^k)=0) (q : K[X]) (hq : q.natDegree≤t) :
    F (q*X^(t-q.natDegree))=q.leadingCoeff * F (X^t) := by
  nth_rw 1 [q.as_sum_range_C_mul_X_pow]
  rw [Finset.sum_mul,map_sum,Finset.sum_range_succ]
  have hlow : (∑ i ∈ Finset.range q.natDegree,
      F (C (q.coeff i)*X^i*X^(t-q.natDegree)))=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [mul_assoc,← pow_add,← Polynomial.smul_eq_C_mul,map_smul,
      hzero _ (by have := Finset.mem_range.mp hi; omega),smul_zero]
  rw [hlow,zero_add,mul_assoc,← pow_add,Nat.add_sub_of_le hq,
    ← Polynomial.smul_eq_C_mul,map_smul,Polynomial.coeff_natDegree]
  rfl

/-- A first failed relation at `t` forces every original kernel polynomial
`p*q` to have quotient degree below `t-m`. -/
theorem kernel_quotient_degree_bound (L : K[X] →ₗ[K] K) (m t : ℕ)
    (p q : K[X]) (hp : p≠0) (hq : q≠0) (hdegree : (p*q).natDegree≤m)
    (ht : m<t) (hzero : ∀ j<t, L (p*X^j)=0) (hfail : L (p*X^t)≠0)
    (hann : ∀ j≤m, L ((p*q)*X^j)=0) : q.natDegree<t-m := by
  have hqdeg : q.natDegree≤m := by
    rw [Polynomial.natDegree_mul hp hq] at hdegree
    omega
  by_contra hbound
  have hj : t-q.natDegree≤m := by omega
  have h := first_nonzero_moment_detects_top (jetMultiply p L) t hzero q (by omega)
  change L (p*(q*X^(t-q.natDegree))) = q.leadingCoeff * L (p*X^t) at h
  rw [← mul_assoc,hann _ hj] at h
  exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hq) hfail) h.symm

end OddZeta.FourValue

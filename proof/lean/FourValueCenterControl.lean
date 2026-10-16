import FourValueLatticeSupport
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-! Construction of canonical finite jet families and uniqueness from the
center component for the exact four-value Pearson polynomial. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K]

theorem finite_functional_jet_family (p : K[X]) (hp : p≠0) (hsplit : p.Splits)
    (U : K[X] →ₗ[K] K) (hU : Annihilates U p) :
    ∃ (J : JetFamily K) (d : ℕ), realizeJets J=U ∧ JetsBound J d := by
  classical
  obtain ⟨s,b,V,hV,hbound⟩ := finite_functional_jet_decomposition p hp hsplit U hU
  let J : JetFamily K := ∑ a ∈ s, Finsupp.single a (V a)
  have hJ (a : K) : J a = if a ∈ s then V a else 0 := by
    simp [J, Finsupp.sum_apply, Finsupp.single_apply]
  refine ⟨J,s.sup b,?_,?_⟩
  · dsimp [J]
    rw [map_sum]
    simp only [realizeJets_single]
    exact hV.symm
  · intro a k hk
    rw [hJ]
    split_ifs with ha
    · exact hbound a ha k (lt_of_le_of_lt (Finset.le_sup ha) hk)
    · rfl

/-- Every finite complex Pearson functional is represented by an actual
finite jet family with a common bound. -/
theorem complex_finitePearson_jet_family (A : ℂ[X]) (U : ℂ[X] →ₗ[ℂ] ℂ)
    (hU : IsFinitePearson A U) :
    ∃ (J : JetFamily ℂ) (d : ℕ), realizeJets J=U ∧ JetsBound J d := by
  obtain ⟨p,hp,hann⟩ := hU.1
  exact finite_functional_jet_family p hp (IsAlgClosed.splits p) U hann

/-- Finite Pearson solutions are closed under subtraction; the product of
the two annihilators annihilates the difference. -/
theorem IsFinitePearson.sub [CharZero K] (A : K[X]) (U V : K[X] →ₗ[K] K)
    (hU : IsFinitePearson A U) (hV : IsFinitePearson A V) :
    IsFinitePearson A (U-V) := by
  obtain ⟨p,hp,hpU⟩ := hU.1
  obtain ⟨q,hq,hqV⟩ := hV.1
  refine ⟨⟨p*q,mul_ne_zero hp hq,?_⟩,?_,?_⟩
  · intro f
    change U ((p*q)*f)-V ((p*q)*f)=0
    have h₁ : U ((p*q)*f)=0 := by rw [mul_assoc]; exact hpU _
    have h₂ : V ((p*q)*f)=0 := by rw [mul_comm p q, mul_assoc]; exact hqV _
    rw [h₁,h₂,sub_self]
  · intro f
    simp only [LinearMap.sub_apply, hU.2.1, hV.2.1]
    ring
  · intro f
    simp [hU.2.2 f,hV.2.2 f]

/-- Every nonempty support chain crosses the origin. This uses the actual
endpoint bounds, not an assumed lattice-support condition. -/
theorem finitePearson_nonzero_center [CharZero K] (n : ℕ) (J : JetFamily K) (d : ℕ)
    (hJ : JetsBound J d)
    (hU : IsFinitePearson (pearsonPolynomial (n:K)) (realizeJets J))
    (a : K) (ha : J a≠0) : J 0≠0 := by
  obtain ⟨k,hk,hforward⟩ := finitePearson_forward_endpoint _ J d hJ hU a ha
  obtain ⟨l,hl,hbackward⟩ := finitePearson_backward_endpoint _ J d hJ hU a ha
  obtain ⟨t,ht,htr⟩ := pearson_root_integer n _ hk
  obtain ⟨u,hu,hur⟩ := pearson_root_integer n _ hl
  have hsumK : (t:K)+(u:K)=(k:K)+(l:K) := by linear_combination -(ht+hu)/2
  have hsum : t+u=(k:ℤ)+l := by exact_mod_cast hsumK
  obtain ⟨ht0,htb,hu0,hub⟩ := admissible_root_pair_nonnegative n k l t u htr hur hsum
  by_cases hsign : (k:ℤ)≤t
  · let j : ℕ := (t-(k:ℤ)).toNat
    have hjcast : (j:ℤ)=t-(k:ℤ) := Int.toNat_of_nonneg (by omega)
    have hj : j≤l := by omega
    have hzero : a-2*(j:K)=0 := by
      have hjK : (j:K)=(t:K)-(k:K) := by exact_mod_cast hjcast
      rw [hjK]
      linear_combination ht
    simpa [hzero] using hbackward j hj
  · let j : ℕ := ((k:ℤ)-t).toNat
    have hjcast : (j:ℤ)=(k:ℤ)-t := Int.toNat_of_nonneg (by omega)
    have hj : j≤k := by omega
    have hzero : a+2*(j:K)=0 := by
      have hjK : (j:K)=(k:K)-(t:K) := by exact_mod_cast hjcast
      rw [hjK]
      linear_combination ht
    simpa [hzero] using hforward j hj

/-- The center component determines a finite Pearson solution uniquely. -/
theorem finitePearson_center_injective [CharZero K] (n : ℕ)
    (J J' : JetFamily K) (d : ℕ) (hJ : JetsBound J d) (hJ' : JetsBound J' d)
    (hU : IsFinitePearson (pearsonPolynomial (n:K)) (realizeJets J))
    (hU' : IsFinitePearson (pearsonPolynomial (n:K)) (realizeJets J'))
    (hcenter : J 0=J' 0) : J=J' := by
  apply sub_eq_zero.mp
  have hdiff : IsFinitePearson (pearsonPolynomial (n:K)) (realizeJets (J-J')) := by
    rw [show realizeJets (J-J')=realizeJets J-realizeJets J' from
      (realizeJets (K:=K)).map_sub J J']
    exact IsFinitePearson.sub _ _ _ hU hU'
  apply Finsupp.ext
  intro a
  by_contra ha
  have hzero := finitePearson_nonzero_center n (J-J') d
    (fun a => jetBound_sub (J a) (J' a) d (hJ a) (hJ' a)) hdiff a ha
  exact hzero (by simp [hcenter])

end OddZeta.FourValue

import FourValueJetFamilies
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-! Finite support chains terminate at roots in both directions. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- A finite jet family cannot contain a whole nonconstant arithmetic ray. -/
theorem jetFamily_ray_has_zero (J : JetFamily K) (a c : K) (hc : c ≠ 0) :
    ∃ k : ℕ, J (a+c*k)=0 := by
  classical
  by_contra h
  push Not at h
  have hinj : Function.Injective (fun k : ℕ => a+c*(k:K)) := by
    intro j k heq
    apply Nat.cast_injective (R:=K)
    exact mul_left_cancel₀ hc (add_left_cancel heq)
  have hsub : Set.range (fun k : ℕ => a+c*(k:K)) ⊆ (J.support : Set K) := by
    rintro x ⟨k,rfl⟩
    exact Finsupp.mem_support_iff.mpr (h k)
  exact (Set.infinite_range_of_injective hinj) (J.support.finite_toSet.subset hsub)

/-- A nonzero jet followed by zero can occur only at a root of `A`. -/
theorem finitePearson_terminal_root (A : K[X]) (J : JetFamily K) (d : ℕ)
    (hJ : JetsBound J d) (hU : IsFinitePearson A (realizeJets J))
    (a : K) (ha : J a ≠ 0) (hnext : J (a+2)=0) : A.eval a=0 := by
  by_contra hA
  apply ha
  have hstep := finitePearson_local_transport A J d hJ hU a
  have hz : jetMultiply (Polynomial.taylor a A) (J a)=0 := by
    rw [hnext] at hstep
    exact hstep
  apply jetMultiply_unit_kernel d (J a) (hJ a) _ _ hz
  simpa [Polynomial.taylor_coeff_zero] using hA

/-- The first point of a nonzero chain is the negative of a root of `A`. -/
theorem finitePearson_initial_root (A : K[X]) (J : JetFamily K) (d : ℕ)
    (hJ : JetsBound J d) (hU : IsFinitePearson A (realizeJets J))
    (a : K) (ha : J a ≠ 0) (hprev : J (a-2)=0) : A.eval (-a)=0 := by
  by_contra hA
  apply ha
  have hstep := finitePearson_local_transport A J d hJ hU (a-2)
  rw [sub_add_cancel, hprev] at hstep
  have hz : jetMultiply (Polynomial.taylor a (A.comp (-X))) (J a)=0 := hstep.symm
  apply jetMultiply_unit_kernel d (J a) (hJ a) _ _ hz
  simpa [Polynomial.taylor_coeff_zero] using hA

/-- Every support point belongs to a finite forward chain ending at a root.
All intermediate points of the chain carry nonzero jets. -/
theorem finitePearson_forward_endpoint (A : K[X]) (J : JetFamily K) (d : ℕ)
    (hJ : JetsBound J d) (hU : IsFinitePearson A (realizeJets J))
    (a : K) (ha : J a ≠ 0) :
    ∃ k : ℕ, A.eval (a+2*k)=0 ∧ ∀ j ≤ k, J (a+2*j)≠0 := by
  classical
  have hex := jetFamily_ray_has_zero J a 2 (by norm_num)
  let N := Nat.find hex
  have hN : 0<N := by
    apply (Nat.find_pos hex).mpr
    simpa using ha
  have hz : J (a+2*(N:K))=0 := Nat.find_spec hex
  have hbefore : ∀ j<N, J (a+2*(j:K))≠0 := fun j hj => Nat.find_min hex hj
  refine ⟨N-1, ?_, fun j hj => hbefore j (by omega)⟩
  apply finitePearson_terminal_root A J d hJ hU _ (hbefore (N-1) (by omega))
  have hcast : ((N-1:ℕ):K)+1=(N:K) := by exact_mod_cast (Nat.sub_add_cancel hN)
  have heq : a+2*((N-1:ℕ):K)+2=a+2*(N:K) := by rw [← hcast]; ring
  rwa [heq]

/-- The backward chain ends at the negative of a root. -/
theorem finitePearson_backward_endpoint (A : K[X]) (J : JetFamily K) (d : ℕ)
    (hJ : JetsBound J d) (hU : IsFinitePearson A (realizeJets J))
    (a : K) (ha : J a ≠ 0) :
    ∃ k : ℕ, A.eval (-a+2*k)=0 ∧ ∀ j ≤ k, J (a-2*j)≠0 := by
  classical
  have hex : ∃ k : ℕ, J (a-2*(k:K))=0 := by
    simpa [sub_eq_add_neg] using jetFamily_ray_has_zero J a (-2) (by norm_num)
  let N := Nat.find hex
  have hN : 0<N := by
    apply (Nat.find_pos hex).mpr
    simpa using ha
  have hz : J (a-2*(N:K))=0 := Nat.find_spec hex
  have hbefore : ∀ j<N, J (a-2*(j:K))≠0 := fun j hj => Nat.find_min hex hj
  refine ⟨N-1, ?_, fun j hj => hbefore j (by omega)⟩
  have hroot := finitePearson_initial_root A J d hJ hU (a-2*((N-1:ℕ):K))
    (hbefore (N-1) (by omega))
  have hcast : ((N-1:ℕ):K)+1=(N:K) := by exact_mod_cast (Nat.sub_add_cancel hN)
  have heq : a-2*((N-1:ℕ):K)-2=a-2*(N:K) := by rw [← hcast]; ring
  have hp : J (a-2*((N-1:ℕ):K)-2)=0 := by rwa [heq]
  have harg : -(a-2*((N-1:ℕ):K)) = -a+2*((N-1:ℕ):K) := by ring
  rw [harg] at hroot
  exact hroot hp

end OddZeta.FourValue

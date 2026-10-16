import FourValueJetTransport
import FourValueReflection
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

/-! Canonical finite jet families and extraction of local Pearson transport. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K]

abbrev JetFamily (K : Type*) [Field K] := K →₀ (K[X] →ₗ[K] K)

def realizeJets : JetFamily K →ₗ[K] (K[X] →ₗ[K] K) :=
  Finsupp.lsum K (fun a => LinearMap.lcomp K K (Polynomial.taylor a))

@[simp] theorem realizeJets_single (a : K) (U : K[X] →ₗ[K] K) :
    realizeJets (Finsupp.single a U) = jetAt a U := by
  rw [realizeJets, Finsupp.lsum_single]
  rfl

def JetsBound (J : JetFamily K) (d : ℕ) : Prop := ∀ a : K, JetBound (J a) d

theorem realizeJets_zero (J : JetFamily K) (d : ℕ) (hJ : JetsBound J d)
    (hz : realizeJets J=0) : J=0 := by
  classical
  have hsum : ∑ a ∈ J.support, jetAt a (J a) = 0 := hz
  have hall := finite_jets_sum_zero J.support (fun a => J a) (fun _ => d)
    (fun a _ => hJ a) hsum
  apply Finsupp.ext
  intro a
  by_cases ha : a ∈ J.support
  · exact hall a ha
  · exact Finsupp.notMem_support_iff.mp ha

theorem realizeJets_injective (J J' : JetFamily K) (d : ℕ)
    (hJ : JetsBound J d) (hJ' : JetsBound J' d)
    (heq : realizeJets J=realizeJets J') : J=J' := by
  apply sub_eq_zero.mp
  apply realizeJets_zero (J-J') d
  · intro a
    exact jetBound_sub (J a) (J' a) d (hJ a) (hJ' a)
  · rw [show realizeJets (J-J') = realizeJets J - realizeJets J' from
      (realizeJets (K:=K)).map_sub J J', heq, sub_self]

def jetMulMap (p : K[X]) : (K[X] →ₗ[K] K) →ₗ[K] (K[X] →ₗ[K] K) where
  toFun := jetMultiply p
  map_add' U V := by ext f; simp [jetMultiply_apply]
  map_smul' c U := by ext f; simp [jetMultiply_apply]

def weightedJets (A : K[X]) : JetFamily K →ₗ[K] JetFamily K :=
  Finsupp.lsum K (fun a => (Finsupp.lsingle a).comp
    (jetMulMap (Polynomial.taylor a A)))

@[simp] theorem weightedJets_single (A : K[X]) (a : K) (U : K[X] →ₗ[K] K) :
    weightedJets A (Finsupp.single a U) =
      Finsupp.single a (jetMultiply (Polynomial.taylor a A) U) := by
  simp [weightedJets, Finsupp.lsum_single, jetMulMap]

@[simp] theorem weightedJets_apply (A : K[X]) (J : JetFamily K) (a : K) :
    weightedJets A J a = jetMultiply (Polynomial.taylor a A) (J a) := by
  classical
  have h : (Finsupp.lapply a).comp (weightedJets A) =
      (jetMulMap (Polynomial.taylor a A)).comp (Finsupp.lapply a) := by
    apply Finsupp.lhom_ext
    intro b U
    by_cases hab : a=b
    · subst b
      simp [jetMulMap]
    · simp [hab, jetMulMap]
      rfl
  exact LinearMap.congr_fun h J

theorem weightedJets_bound (A : K[X]) (J : JetFamily K) (d : ℕ)
    (hJ : JetsBound J d) : JetsBound (weightedJets A J) d := by
  intro a
  rw [weightedJets_apply]
  exact jetBound_multiply (J a) d (hJ a) _

theorem realizeJets_weighted (A : K[X]) (J : JetFamily K) :
    realizeJets (weightedJets A J) = jetMultiply A (realizeJets J) := by
  have h : realizeJets.comp (weightedJets A) = (jetMulMap A).comp realizeJets := by
    apply Finsupp.lhom_ext
    intro a U
    simp only [LinearMap.comp_apply, weightedJets_single, realizeJets_single]
    exact (jetAt_multiply a U A).symm
  exact LinearMap.congr_fun h J

def shiftJets (c : K) : JetFamily K →ₗ[K] JetFamily K :=
  Finsupp.lmapDomain _ K (fun a => a+c)

@[simp] theorem shiftJets_single (c a : K) (U : K[X] →ₗ[K] K) :
    shiftJets c (Finsupp.single a U) = Finsupp.single (a+c) U := by
  simp [shiftJets]

@[simp] theorem shiftJets_apply (c : K) (J : JetFamily K) (a : K) :
    shiftJets c J a = J (a-c) := by
  have h := Finsupp.mapDomain_apply (fun x y (h : x+c=y+c) => add_right_cancel h) J (a-c)
  simpa [shiftJets, Finsupp.lmapDomain_apply] using h

theorem shiftJets_bound (c : K) (J : JetFamily K) (d : ℕ)
    (hJ : JetsBound J d) : JetsBound (shiftJets c J) d := by
  intro a
  rw [shiftJets_apply]
  exact hJ _

theorem realizeJets_shift (c : K) (J : JetFamily K) :
    realizeJets (shiftJets c J) = (realizeJets J).comp (Polynomial.taylor c) := by
  have h : realizeJets.comp (shiftJets c) =
      (LinearMap.lcomp K K (Polynomial.taylor c)).comp realizeJets := by
    apply Finsupp.lhom_ext
    intro a U
    simp only [LinearMap.comp_apply, shiftJets_single, realizeJets_single,
      LinearMap.lcomp_apply']
    apply LinearMap.ext
    intro f
    simp [jetAt, Polynomial.taylor_taylor]
  exact LinearMap.congr_fun h J

/-- The two odd reflection identities compose to the translation equation. -/
theorem finitePearson_translation [CharZero K] (A : K[X]) (U : K[X] →ₗ[K] K)
    (hU : IsFinitePearson A U) (f : K[X]) :
    U (A*f) = U (A.comp (-X) * f.comp (X-2)) := by
  have hτ := finitePearson_affine_reflection A U hU f
  have hσ := hU.2.1 (A * f.comp (-X-2))
  have heq : (A * f.comp (-X-2)).comp (-X) =
      A.comp (-X) * f.comp (X-2) := by
    simp [Polynomial.mul_comp, Polynomial.comp_assoc]
  rw [heq, hτ, neg_neg] at hσ
  exact hσ.symm

/-- Extract the actual local transport equation at every complex point from
the global finite Pearson identities and uniqueness of jet components. -/
theorem finitePearson_local_transport [CharZero K] (A : K[X]) (J : JetFamily K)
    (d : ℕ) (hJ : JetsBound J d) (hU : IsFinitePearson A (realizeJets J)) (a : K) :
    jetMultiply (Polynomial.taylor a A) (J a) =
      jetMultiply (Polynomial.taylor (a+2) (A.comp (-X))) (J (a+2)) := by
  have heq : weightedJets A J = shiftJets (-2) (weightedJets (A.comp (-X)) J) := by
    apply realizeJets_injective _ _ d (weightedJets_bound A J d hJ)
      (shiftJets_bound _ _ d (weightedJets_bound _ J d hJ))
    rw [realizeJets_shift, realizeJets_weighted, realizeJets_weighted]
    apply LinearMap.ext
    intro f
    change realizeJets J (A*f) = realizeJets J
      (A.comp (-X) * Polynomial.taylor (-2) f)
    have hC : (C (2:K):K[X]) = 2 := by
      rw [show (2:K)=1+1 by ring, map_add, map_one]
      ring
    simpa [Polynomial.taylor_apply, sub_eq_add_neg, hC] using finitePearson_translation A (realizeJets J) hU f
  have h := congrArg (fun F : JetFamily K => F a) heq
  simpa using h

end OddZeta.FourValue

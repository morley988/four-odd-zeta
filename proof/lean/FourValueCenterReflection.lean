import FourValueCenterControl
import Mathlib.Tactic

/-! Reflection of finite jet families and oddness of the center jet. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K]

def polynomialReflect : K[X] →ₗ[K] K[X] where
  toFun f := f.comp (-X)
  map_add' _ _ := Polynomial.add_comp
  map_smul' _ _ := by simp

def reflectJetMap : (K[X] →ₗ[K] K) →ₗ[K] (K[X] →ₗ[K] K) :=
  LinearMap.lcomp K K polynomialReflect

@[simp] theorem reflectJetMap_apply (U : K[X] →ₗ[K] K) (f : K[X]) :
    reflectJetMap U f = U (f.comp (-X)) := rfl

def reflectedJets : JetFamily K →ₗ[K] JetFamily K :=
  (Finsupp.lmapDomain _ K (fun a : K => -a)).comp
    (Finsupp.mapRange.linearMap reflectJetMap)

@[simp] theorem reflectedJets_single (a : K) (U : K[X] →ₗ[K] K) :
    reflectedJets (Finsupp.single a U) = Finsupp.single (-a) (reflectJetMap U) := by
  simp [reflectedJets]

@[simp] theorem reflectedJets_apply (J : JetFamily K) (a : K) :
    reflectedJets J a = reflectJetMap (J (-a)) := by
  have h := Finsupp.mapDomain_apply (neg_injective : Function.Injective (fun a : K => -a))
    ((Finsupp.mapRange.linearMap reflectJetMap) J) (-a)
  simpa [reflectedJets, Finsupp.lmapDomain_apply] using h

theorem reflectJetMap_bound (U : K[X] →ₗ[K] K) (d : ℕ) (hU : JetBound U d) :
    JetBound (reflectJetMap U) d := by
  intro k hk
  rw [reflectJetMap_apply]
  rcases Nat.even_or_odd k with heven | hodd
  · simp [Polynomial.pow_comp, heven.neg_pow, hU k hk]
  · simp [Polynomial.pow_comp, hodd.neg_pow, hU k hk]

theorem reflectedJets_bound (J : JetFamily K) (d : ℕ) (hJ : JetsBound J d) :
    JetsBound (reflectedJets J) d := by
  intro a
  rw [reflectedJets_apply]
  exact reflectJetMap_bound _ d (hJ _)

theorem realizeJets_reflected (J : JetFamily K) :
    realizeJets (reflectedJets J) = reflectJetMap (realizeJets J) := by
  have h : (realizeJets (K:=K)).comp reflectedJets = reflectJetMap.comp realizeJets := by
    apply Finsupp.lhom_ext
    intro a U
    simp only [LinearMap.comp_apply, reflectedJets_single, realizeJets_single]
    apply LinearMap.ext
    intro f
    simp only [jetAt_apply, reflectJetMap_apply, Polynomial.taylor_apply,
      Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp,
      Polynomial.C_comp, Polynomial.neg_comp]
    congr 2
    simp [add_comm]
  exact LinearMap.congr_fun h J

/-- Global oddness descends to the actual center component. -/
theorem finitePearson_center_odd [CharZero K] (A : K[X]) (J : JetFamily K) (d : ℕ)
    (hJ : JetsBound J d) (hU : IsFinitePearson A (realizeJets J)) :
    ∀ f : K[X], J 0 (f.comp (-X)) = -J 0 f := by
  have heq : reflectedJets J = -J := by
    apply realizeJets_injective _ _ d (reflectedJets_bound J d hJ)
    · intro a k hk
      simp [hJ a k hk]
    · rw [realizeJets_reflected, (realizeJets (K:=K)).map_neg J]
      apply LinearMap.ext
      intro f
      exact hU.2.1 f
  have hcenter := congrArg (fun F : JetFamily K => F 0) heq
  simp only [reflectedJets_apply, neg_zero, Finsupp.neg_apply] at hcenter
  intro f
  exact LinearMap.congr_fun hcenter f

end OddZeta.FourValue

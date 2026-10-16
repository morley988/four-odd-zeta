import FourValueCenterOrder
import FourValueCenterReflection
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

/-! The actual finite Pearson space embeds linearly in seven center
coordinates. This is an unconditional upper bound, not yet the residue
identification of its restrictions to the first nine moments. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem IsFinitePearson.smul (A : K[X]) (U : K[X] →ₗ[K] K)
    (hU : IsFinitePearson A U) (c : K) : IsFinitePearson A (c • U) := by
  obtain ⟨p,hp,hann⟩ := hU.1
  refine ⟨⟨p,hp,?_⟩,?_,?_⟩
  · intro f
    simp [hann f]
  · intro f
    simp [hU.2.1 f]
  · intro f
    simp [hU.2.2 f]

theorem IsFinitePearson.add (A : K[X]) (U V : K[X] →ₗ[K] K)
    (hU : IsFinitePearson A U) (hV : IsFinitePearson A V) :
    IsFinitePearson A (U+V) := by
  have h := IsFinitePearson.sub A U ((-1:K)•V) hU (hV.smul A V (-1))
  have heq : U-(-1:K)•V=U+V := by
    apply LinearMap.ext
    intro f
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    ring
  rwa [heq] at h

def finitePearsonSpace (A : K[X]) : Submodule K (K[X] →ₗ[K] K) where
  carrier := {U | IsFinitePearson A U}
  zero_mem' := by exact ⟨⟨1,one_ne_zero,by simp⟩,by simp,by simp⟩
  add_mem' := fun hU hV => IsFinitePearson.add A _ _ hU hV
  smul_mem' := fun c _ hU => IsFinitePearson.smul A _ hU c

theorem JetsBound.mono {J : JetFamily K} {d e : ℕ} (hJ : JetsBound J d) (hde : d≤e) :
    JetsBound J e := fun a k hk => hJ a k (by omega)

theorem JetsBound.add {J J' : JetFamily K} {d : ℕ}
    (hJ : JetsBound J d) (hJ' : JetsBound J' d) : JetsBound (J+J') d := by
  intro a k hk
  simp [hJ a k hk,hJ' a k hk]

theorem JetsBound.smul {J : JetFamily K} {d : ℕ}
    (hJ : JetsBound J d) (c : K) : JetsBound (c•J) d := by
  intro a k hk
  simp [hJ a k hk]

def chosenPearsonJets (A : ℂ[X]) (U : finitePearsonSpace A) : JetFamily ℂ :=
  Classical.choose (complex_finitePearson_jet_family A U U.property)

theorem chosenPearsonJets_spec (A : ℂ[X]) (U : finitePearsonSpace A) :
    ∃ d : ℕ, realizeJets (chosenPearsonJets A U)=U.val ∧
      JetsBound (chosenPearsonJets A U) d :=
  Classical.choose_spec (complex_finitePearson_jet_family A U U.property)

/-- The center extraction is a linear map; arbitrary choices in the
existence proof disappear by uniqueness of finite jet decompositions. -/
def pearsonCenterMap (A : ℂ[X]) : finitePearsonSpace A →ₗ[ℂ] (ℂ[X] →ₗ[ℂ] ℂ) where
  toFun U := chosenPearsonJets A U 0
  map_add' U V := by
    obtain ⟨d,hUV,bUV⟩ := chosenPearsonJets_spec A (U+V)
    obtain ⟨e,hU,bU⟩ := chosenPearsonJets_spec A U
    obtain ⟨f,hV,bV⟩ := chosenPearsonJets_spec A V
    have heq := realizeJets_injective (chosenPearsonJets A (U+V))
      (chosenPearsonJets A U + chosenPearsonJets A V) (max d (max e f))
      (bUV.mono (by omega)) ((bU.mono (by omega)).add (bV.mono (by omega)))
      (by rw [(realizeJets (K:=ℂ)).map_add, hUV,hU,hV]; rfl)
    exact congrArg (fun J : JetFamily ℂ => J 0) heq
  map_smul' c U := by
    obtain ⟨d,hcU,bcU⟩ := chosenPearsonJets_spec A (c•U)
    obtain ⟨e,hU,bU⟩ := chosenPearsonJets_spec A U
    have heq := realizeJets_injective (chosenPearsonJets A (c•U))
      (c•chosenPearsonJets A U) (max d e)
      (bcU.mono (by omega)) ((bU.mono (by omega)).smul c)
      (by rw [(realizeJets (K:=ℂ)).map_smul, hcU,hU]; rfl)
    exact congrArg (fun J : JetFamily ℂ => J 0) heq

/-- The exact Pearson space is already determined by its center jet. -/
theorem pearsonCenterMap_injective (n : ℕ) :
    Function.Injective (pearsonCenterMap (pearsonPolynomial (n:ℂ))) := by
  intro U V hcenter
  let A := pearsonPolynomial (n:ℂ)
  obtain ⟨d,hU,bU⟩ := chosenPearsonJets_spec A U
  obtain ⟨e,hV,bV⟩ := chosenPearsonJets_spec A V
  have hu : IsFinitePearson A (realizeJets (chosenPearsonJets A U)) := hU ▸ U.property
  have hv : IsFinitePearson A (realizeJets (chosenPearsonJets A V)) := hV ▸ V.property
  have heq := finitePearson_center_injective n (chosenPearsonJets A U)
    (chosenPearsonJets A V) (max d e) (bU.mono (by omega)) (bV.mono (by omega)) hu hv hcenter
  apply Subtype.ext
  rw [← hU,← hV,heq]

/-- Seven coefficient moments give an explicit linear embedding. -/
def pearsonCoordinates (n : ℕ) :
    finitePearsonSpace (pearsonPolynomial (n:ℂ)) →ₗ[ℂ] (Fin 7 → ℂ) where
  toFun U i := pearsonCenterMap _ U (X^(2*i.val+1))
  map_add' U V := by ext i; simp
  map_smul' c U := by ext i; simp

theorem pearsonCenterMap_expansion (n : ℕ)
    (U : finitePearsonSpace (pearsonPolynomial (n:ℂ))) :
    pearsonCenterMap _ U = ∑ i : Fin 7, pearsonCoordinates n U i • centerJetBasis i := by
  obtain ⟨d,hU,bU⟩ := chosenPearsonJets_spec _ U
  have hu : IsFinitePearson (pearsonPolynomial (n:ℂ))
      (realizeJets (chosenPearsonJets _ U)) := hU ▸ U.property
  exact odd_jet_center_expansion _
    (finitePearson_center_order_bound n _ d bU hu)
    (finitePearson_center_odd _ _ d bU hu)

theorem pearsonCoordinates_injective (n : ℕ) : Function.Injective (pearsonCoordinates n) := by
  intro U V h
  apply pearsonCenterMap_injective n
  rw [pearsonCenterMap_expansion,pearsonCenterMap_expansion,h]

/-- The space is genuinely finite-dimensional, rather than merely having
finrank zero by the infinite-dimensional convention. -/
theorem finitePearsonSpace_finiteDimensional (n : ℕ) :
    FiniteDimensional ℂ (finitePearsonSpace (pearsonPolynomial (n:ℂ))) :=
  FiniteDimensional.of_injective (pearsonCoordinates n) (pearsonCoordinates_injective n)

/-- Unconditional seven-dimensional upper bound for the actual complex
finite Pearson space. Surjectivity / the seven residue solutions are not
asserted by this theorem. -/
theorem finitePearsonSpace_finrank_le_seven (n : ℕ) :
    Module.finrank ℂ (finitePearsonSpace (pearsonPolynomial (n:ℂ))) ≤ 7 := by
  have h := LinearMap.finrank_le_finrank_of_injective (pearsonCoordinates_injective n)
  simpa using h

end OddZeta.FourValue

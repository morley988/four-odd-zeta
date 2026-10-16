import FourValueTargetRestrictions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Exact finite Pearson restriction classification. The seven-dimensional
bound is sharp globally, but one nonzero residue functional vanishes on
the first nine lifted moments. The remaining six independent directions
are precisely B3, B5, B7, B9, C1, C3. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial

theorem range_eq_six_span_of_kernel {K E V : Type*} [Field K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (R : E →ₗ[K] V) (hE : Module.finrank K E≤7)
    (v : Fin 6 → V) (hv : LinearIndependent K v)
    (hr : ∀ i,v i∈R.range) (hk : ∃ u∈R.ker,u≠0) :
    R.range=Submodule.span K (Set.range v) := by
  have hle : Submodule.span K (Set.range v)≤R.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hr i
  have hd : Module.finrank K (Submodule.span K (Set.range v))=6 := by
    simpa using finrank_span_eq_card hv
  have hker : 0<Module.finrank K R.ker := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    obtain ⟨u,hu,hne⟩ := hk
    refine ⟨⟨u,hu⟩,?_⟩
    intro hz
    exact hne (congrArg Subtype.val hz)
  have hdim := R.finrank_range_add_finrank_ker
  exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm

/-- No residue classification hypothesis remains: this is the exact image
of all finite odd Pearson solutions, for the specified target family. -/
theorem finitePearson_restriction_classification (n : ℕ) (hn : 1≤n) :
    (finitePearsonRestriction n).range = Submodule.span ℂ
      (Set.range (fun i : Fin 6 => targetPhysicalRow n (restrictionRowIndex i))) := by
  letI := finitePearsonSpace_finiteDimensional n
  apply range_eq_six_span_of_kernel (finitePearsonRestriction n)
    (finitePearsonSpace_finrank_le_seven n)
  · exact (targetPhysicalRow_independent (K:=ℂ) n hn).comp restrictionRowIndex restrictionRowIndex_injective
  · exact target_six_in_restriction_range n hn
  · exact target_restriction_kernel_nonzero n hn

theorem finitePearson_restriction_finrank (n : ℕ) (hn : 1≤n) :
    Module.finrank ℂ (finitePearsonRestriction n).range=6 := by
  rw [finitePearson_restriction_classification n hn]
  simpa only [Function.comp_def,Fintype.card_fin] using finrank_span_eq_card
    ((targetPhysicalRow_independent (K:=ℂ) n hn).comp restrictionRowIndex restrictionRowIndex_injective)

theorem finitePearsonSpace_finrank_eq_seven (n : ℕ) (hn : 1≤n) :
    Module.finrank ℂ (finitePearsonSpace (pearsonPolynomial (n:ℂ)))=7 := by
  letI := finitePearsonSpace_finiteDimensional n
  have hdim := (finitePearsonRestriction n).finrank_range_add_finrank_ker
  have hr := finitePearson_restriction_finrank n hn
  have hb := finitePearsonSpace_finrank_le_seven n
  have hk : 0<Module.finrank ℂ (finitePearsonRestriction n).ker := by
    apply (Module.finrank_pos_iff_exists_ne_zero (R:=ℂ) (M:=(finitePearsonRestriction n).ker)).mpr
    obtain ⟨u,hu,hne⟩ := target_restriction_kernel_nonzero n hn
    refine ⟨⟨u,hu⟩,?_⟩
    intro hz
    exact hne (congrArg Subtype.val hz)
  omega

theorem finitePearson_restriction_iff (n : ℕ) (hn : 1≤n) (w : Fin 9 → ℂ) :
    (∃ U : ℂ[X] →ₗ[ℂ] ℂ, IsFinitePearson (pearsonPolynomial (n:ℂ)) U ∧
      liftedInitialMoments U=w) ↔
    w ∈ Submodule.span ℂ (Set.range (fun i : Fin 6 => targetPhysicalRow n (restrictionRowIndex i))) := by
  rw [← finitePearson_restriction_classification n hn]
  constructor
  · rintro ⟨U,hU,h⟩
    exact ⟨⟨U,hU⟩,h⟩
  · rintro ⟨U,h⟩
    exact ⟨U.val,U.property,h⟩

theorem span_range_smul_nonzero {K V I : Type*} [Field K]
    [AddCommGroup V] [Module K V] (v : I → V) (c : K) (hc : c≠0) :
    Submodule.span K (Set.range (fun i => c • v i)) =
      Submodule.span K (Set.range v) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have h := Submodule.smul_mem (Submodule.span K (Set.range (fun i => c • v i)))
      c⁻¹ (Submodule.subset_span (Set.mem_range_self i))
    rw [smul_smul,inv_mul_cancel₀ hc,one_smul] at h
    exact h

/-- The same exact classification with the manuscript's factorial normalization. -/
theorem finitePearson_restriction_classification_normalized (n : ℕ) (hn : 1≤n) :
    (finitePearsonRestriction n).range = Submodule.span ℂ
      (Set.range (fun i : Fin 6 => fun j : Fin 9 =>
        normalizedTargetFunctional n (restrictionRowIndex i) ((C 4*X)^j.val))) := by
  have heq : (fun i : Fin 6 => fun j : Fin 9 =>
        normalizedTargetFunctional (K:=ℂ) n (restrictionRowIndex i) ((C 4*X)^j.val)) =
      (fun i : Fin 6 => targetNormalization (K:=ℂ) n • targetPhysicalRow (K:=ℂ) n (restrictionRowIndex i)) := by
    funext i j
    rw [normalizedTargetFunctional_apply]
    rfl
  rw [heq,span_range_smul_nonzero _ _ (targetNormalization_ne_zero n)]
  exact finitePearson_restriction_classification n hn

theorem finitePearson_restriction_kernel_finrank (n : ℕ) (hn : 1≤n) :
    Module.finrank ℂ (finitePearsonRestriction n).ker=1 := by
  letI := finitePearsonSpace_finiteDimensional n
  have hdim := (finitePearsonRestriction n).finrank_range_add_finrank_ker
  rw [finitePearson_restriction_finrank n hn,finitePearsonSpace_finrank_eq_seven n hn] at hdim
  omega

end OddZeta.FourValue

import FourValueFiniteClassification
import FourValueHankelExtension
import FourValueSquareBasis

/-! Concrete uniform Hankel rank and nonzero-minor selection. All finite
Pearson classification and initial independence inputs are discharged. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial

/-- The normalized observation as a functional in physical X=4Y coordinates. -/
def physicalTargetFunctional (n : ℕ) (i : Fin 9) : ℂ[X] →ₗ[ℂ] ℂ where
  toFun p := normalizedTargetFunctional n i (p.comp (C 4*X))
  map_add' p q := by simp [Polynomial.add_comp]
  map_smul' c p := by simp [Polynomial.smul_comp]

def targetPencil (n : ℕ) (c : Fin 9 → ℂ) : ℂ[X] →ₗ[ℂ] ℂ :=
  ∑ i, c i • physicalTargetFunctional n i

theorem physicalTargetFunctional_monomial (n : ℕ) (i : Fin 9) (j : ℕ) :
    physicalTargetFunctional n i (X^j) =
      normalizedTargetFunctional n i ((C 4*X)^j) := by
  simp [physicalTargetFunctional,Polynomial.pow_comp]

theorem targetPencil_initial (n : ℕ) (c : Fin 9 → ℂ) :
    initialMoments (targetPencil n c) = ∑ i, c i •
      (fun j : Fin 9 => normalizedTargetFunctional n i ((C 4*X)^j.val)) := by
  ext j
  simp [initialMoments,targetPencil,physicalTargetFunctional_monomial]

theorem finitePearson_normalized_coordinates (n : ℕ) (hn : 1≤n)
    (U : ℂ[X] →ₗ[ℂ] ℂ) (hU : IsFinitePearson (pearsonPolynomial (n:ℂ)) U) :
    ∃ b : Fin 9 → ℂ, b 8=0 ∧ liftedInitialMoments U = ∑ i, b i •
      (fun j : Fin 9 => normalizedTargetFunctional n i ((C 4*X)^j.val)) := by
  classical
  have hmem : liftedInitialMoments U ∈ (finitePearsonRestriction n).range :=
    ⟨⟨U,hU⟩,rfl⟩
  rw [finitePearson_restriction_classification_normalized n hn] at hmem
  obtain ⟨d,hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  refine ⟨![d 0,d 1,d 2,d 3,0,d 4,0,d 5,0],by simp,?_⟩
  rw [← hd]
  simp [Fin.sum_univ_succ,restrictionRowIndex]

theorem targetPencil_finite_exclusion (n : ℕ) (hn : 1≤n)
    (c : Fin 9 → ℂ) (hc : c 8≠0) :
    ∀ U : ℂ[X] →ₗ[ℂ] ℂ, IsFinitePearson (pearsonPolynomial (n:ℂ)) U →
      liftedInitialMoments U≠initialMoments (targetPencil n c) := by
  exact initial_coordinate_exclusion _ _ _ (normalizedTargetNine_independence n hn)
    c hc (targetPencil_initial n c) (finitePearson_normalized_coordinates n hn)

theorem targetPencil_pearson (n : ℕ) (c : Fin 9 → ℂ) (q : ℂ[X])
    (hq : (q.natDegree:ℤ)+6≤361*(n:ℤ)) :
    targetPencil n c (pearsonOperator (pearsonPolynomial (n:ℂ)) q)=0 := by
  simp only [targetPencil,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i hi
  change c i * normalizedTargetFunctional n i
    ((pearsonOperator (pearsonPolynomial (n:ℂ)) q).comp (C 4*X))=0
  rw [normalizedTargetNine_pearson n q hq i,mul_zero]

/-- Valid for every degree budget 2m <= 361n+3, including the manuscript's m. -/
theorem targetPencil_rank_bound (n : ℕ) (hn : 1≤n) (c : Fin 9 → ℂ)
    (hc : c 8≠0) (m : ℕ) (hm : 2*m≤361*n+3) :
    m+1-4≤(momentHankel (targetPencil n c) m).rank := by
  apply hankel_rank_bound_of_finite_exclusion _ (pearsonPolynomial (n:ℂ)) m
    (le_of_eq (pearsonPolynomial_degree (n:ℂ)))
  · intro j hj
    apply targetPencil_pearson
    simp only [Polynomial.natDegree_X_pow]
    omega
  · exact targetPencil_finite_exclusion n hn c hc

theorem targetPencil_nonzero_minor (n : ℕ) (hn : 1≤n) (c : Fin 9 → ℂ)
    (hc : c 8≠0) (m : ℕ) (hm : 2*m≤361*n+3) :
    ∃ rows cols : Fin (m+1-4) ↪ Fin (m+1),
      ((momentHankel (targetPencil n c) m).submatrix rows cols).det≠0 :=
  rank_selects_nonzero_minor _ (targetPencil_rank_bound n hn c hc m hm)

/-- The exact truncation used for the four-value determinant argument. -/
def targetHankelDegree (n : ℕ) : ℕ := (361*n)/2

theorem targetPencil_uniform_nonvanishing (n : ℕ) (hn : 1≤n)
    (c : Fin 9 → ℂ) (hc : c 8≠0) :
    targetHankelDegree n+1-4 ≤
      (momentHankel (targetPencil n c) (targetHankelDegree n)).rank ∧
    ∃ rows cols : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1),
      ((momentHankel (targetPencil n c) (targetHankelDegree n)).submatrix rows cols).det≠0 := by
  have hm : 2*targetHankelDegree n≤361*n+3 := by
    dsimp [targetHankelDegree]
    omega
  exact ⟨targetPencil_rank_bound n hn c hc _ hm,
    targetPencil_nonzero_minor n hn c hc _ hm⟩

theorem targetPencil_squareBasis_rank (n : ℕ) (hn : 1≤n) (c : Fin 9 → ℂ)
    (hc : c 8≠0) (m : ℕ) (hm : 2*m≤361*n+3) :
    m+1-4≤(squareBasisGram (targetPencil n c) m).rank := by
  rw [squareBasisGram_rank]
  exact targetPencil_rank_bound n hn c hc m hm

theorem targetPencil_squareBasis_minor (n : ℕ) (hn : 1≤n) (c : Fin 9 → ℂ)
    (hc : c 8≠0) (m : ℕ) (hm : 2*m≤361*n+3) :
    ∃ rows cols : Fin (m+1-4) ↪ Fin (m+1),
      ((squareBasisGram (targetPencil n c) m).submatrix rows cols).det≠0 :=
  rank_selects_nonzero_minor _ (targetPencil_squareBasis_rank n hn c hc m hm)

/-- The affine pencil C4 + lambda0 B3 + lambda1 B5 + lambda2 B7 + lambda3 B9.
The later zeta-series identification supplies the particular lambda values. -/
def fourValuePencil (n : ℕ) (lambda : Fin 4 → ℂ) : ℂ[X] →ₗ[ℂ] ℂ :=
  targetPencil n ![lambda 0,lambda 1,lambda 2,lambda 3,0,0,0,0,1]

theorem fourValuePencil_apply (n : ℕ) (lambda : Fin 4 → ℂ) (p : ℂ[X]) :
    fourValuePencil n lambda p = physicalTargetFunctional n 8 p +
      lambda 0 * physicalTargetFunctional n 0 p +
      lambda 1 * physicalTargetFunctional n 1 p +
      lambda 2 * physicalTargetFunctional n 2 p +
      lambda 3 * physicalTargetFunctional n 3 p := by
  simp [fourValuePencil,targetPencil,Fin.sum_univ_succ]
  ring

/-- Uniform nonvanishing in the actual squared-variable basis, with exact
minor order and distinct row/column indices. -/
theorem fourValue_uniform_nonvanishing (n : ℕ) (hn : 1≤n) (lambda : Fin 4 → ℂ) :
    let m := targetHankelDegree n
    m+1-4 ≤ (squareBasisGram (fourValuePencil n lambda) m).rank ∧
    ∃ rows cols : Fin (m+1-4) ↪ Fin (m+1),
      ((squareBasisGram (fourValuePencil n lambda) m).submatrix rows cols).det≠0 := by
  have hm : 2*targetHankelDegree n≤361*n+3 := by
    dsimp [targetHankelDegree]; omega
  have hc : (![lambda 0,lambda 1,lambda 2,lambda 3,0,0,0,0,1] : Fin 9 → ℂ) 8≠0 := by
    simp
  exact ⟨targetPencil_squareBasis_rank n hn _ hc _ hm,
    targetPencil_squareBasis_minor n hn _ hc _ hm⟩

theorem targetHankelDegree_bounds (n : ℕ) (hn : 1≤n) :
    180≤targetHankelDegree n ∧ 177≤targetHankelDegree n+1-4 ∧
    2*targetHankelDegree n≤361*n := by
  dsimp [targetHankelDegree]
  omega

/-- Every product used in a selected minor lies within the degree budget. -/
theorem target_selected_product_degree (n : ℕ)
    (i j : Fin (targetHankelDegree n+1)) :
    ((squareBasisPolynomial (K:=ℂ) i.val)*squareBasisPolynomial j.val).natDegree≤361*n := by
  have hd := Polynomial.natDegree_mul_le
    (p:=squareBasisPolynomial (K:=ℂ) i.val) (q:=squareBasisPolynomial j.val)
  rw [squareBasisPolynomial_degree,squareBasisPolynomial_degree] at hd
  have hi := i.isLt
  have hj := j.isLt
  dsimp [targetHankelDegree] at hi hj
  omega

end OddZeta.FourValue

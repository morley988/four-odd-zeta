import FourValueRectangleRegularPart

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory

theorem poleRectangleIntegrable_sum {ι : Type*} (s : Finset ι) (F : ι→ℂ→ℂ)
    (a : ℂ) (r h : ℝ) (hF : ∀ i∈s,poleRectangleIntegrable (F i) a r h) :
    poleRectangleIntegrable (fun z => ∑ i∈s,F i z) a r h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [poleRectangleIntegrable]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact poleRectangleIntegrable_add _ _ a r h (hF i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

theorem poleRectangleBoundary_sum {ι : Type*} (s : Finset ι) (F : ι→ℂ→ℂ)
    (a : ℂ) (r h : ℝ) (hF : ∀ i∈s,poleRectangleIntegrable (F i) a r h) :
    poleRectangleBoundary (fun z => ∑ i∈s,F i z) a r h=∑ i∈s,poleRectangleBoundary (F i) a r h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [poleRectangleBoundary]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [poleRectangleBoundary_add _ _ a r h (hF i (Finset.mem_insert_self _ _))
      (poleRectangleIntegrable_sum s F a r h (fun j hj => hF j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))]

def contourPolePrincipalTerm (F : ℂ→ℂ) (k : ℤ) (j : Fin 5) (z : ℂ) : ℂ :=
  iteratedPoleSlope F (k:ℂ) j.val k*(z-(k:ℂ))^(-(5-(j.val:ℤ)))

theorem contourPolePrincipalTerm_integrable (F : ℂ→ℂ) (k : ℤ) (j : Fin 5) (T : ℝ) (hT : T≠0) :
    poleRectangleIntegrable (contourPolePrincipalTerm F k j) (k:ℂ) (1/2) T :=
  poleRectangleIntegrable_const_mul _ _ _ _ _ (poleRectangleIntegrable_zpow _ _ _ (by norm_num) hT _)

theorem contourPolePrincipalTerm_boundary (F : ℂ→ℂ) (k : ℤ) (j : Fin 5) (T : ℝ) (hT : 0<T) :
    poleRectangleBoundary (contourPolePrincipalTerm F k j) (k:ℂ) (1/2) T=
      if j=4 then (2*(Real.pi:ℂ)*Complex.I)*iteratedPoleSlope F (k:ℂ) 4 k else 0 := by
  unfold contourPolePrincipalTerm
  rw [poleRectangleBoundary_const_mul]
  have h5 := poleRectangleBoundary_zpow (k:ℂ) (1/2) T (by norm_num) hT.ne' (-5) (by norm_num)
  have h4 := poleRectangleBoundary_zpow (k:ℂ) (1/2) T (by norm_num) hT.ne' (-4) (by norm_num)
  have h3 := poleRectangleBoundary_zpow (k:ℂ) (1/2) T (by norm_num) hT.ne' (-3) (by norm_num)
  have h2 := poleRectangleBoundary_zpow (k:ℂ) (1/2) T (by norm_num) hT.ne' (-2) (by norm_num)
  norm_num at h5 h4 h3 h2
  fin_cases j
  all_goals norm_num [Fin.ext_iff]
  · exact Or.inr h5
  · exact Or.inr h4
  · exact Or.inr h3
  · exact Or.inr h2
  · simp only [← one_div]
    rw [poleRectangleBoundary_simplePole _ _ _ (by norm_num) hT]
    ring

theorem contourIntegrand_pole_decomposition_sum (F : ℂ→ℂ) (k : ℤ) (z : ℂ) (hz : z≠k) :
    F z*contourKernel z=(∑ j : Fin 5,contourPolePrincipalTerm F k j z)+contourPoleRegularPart F k z := by
  rw [contourIntegrand_pole_decomposition F k z hz]
  simp [Fin.sum_univ_succ,contourPolePrincipalTerm,zpow_neg,zpow_natCast,div_eq_mul_inv]
  ring
end OddZeta.FourValue

import FourValueSelectedSingleNode

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K]

/-- Splitting all copies of one list entry keeps its exact multiplicity. -/
theorem linearRootProduct_list_factor (roots : List ℤ) (f : ℤ → K) (a : ℤ) :
    linearRootProduct (roots.map f) =
      (X-C (f a))^(roots.count a)*
        linearRootProduct ((roots.filter (fun t => t≠a)).map f) := by
  induction roots with
  | nil => simp [linearRootProduct]
  | cons t ts ih =>
    by_cases ht : t=a
    · subst t
      simp only [linearRootProduct,List.map_map] at ih ⊢
      simp only [List.map_cons,List.prod_cons,List.count_cons_self,List.filter_cons_of_neg (by simp : ¬decide (a≠a)=true)]
      rw [ih]
      simp [pow_succ,mul_assoc,mul_comm,mul_left_comm]
    · simp only [linearRootProduct,List.map_cons,List.prod_cons] at ih ⊢
      rw [ih]
      simp [List.count_cons,ht,Ne.symm ht,mul_assoc,mul_comm,mul_left_comm]

theorem integerListRoot_remainder_regular (roots : List ℤ) (a : ℤ) :
    (linearRootProduct ((roots.filter (fun t => t≠a)).map (fun t : ℤ => (t:ℚ)))).eval (a:ℚ) ≠ 0 := by
  induction roots with
  | nil => simp [linearRootProduct]
  | cons t ts ih =>
    by_cases ht : t=a
    · simpa [linearRootProduct,ht] using ih
    · have htq : (a:ℚ)-(t:ℚ)≠0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm ht)
      simpa [linearRootProduct,ht] using mul_ne_zero htq ih
end OddZeta.FourValue

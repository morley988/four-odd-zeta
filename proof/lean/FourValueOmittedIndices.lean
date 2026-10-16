import FourValueAnalyticDeterminants

noncomputable section
namespace OddZeta.FourValue

theorem selected_sum_le_total {m k : ℕ} (r : Fin k ↪ Fin (m+1)) :
    (∑ i,(r i).val)≤∑ j : Fin (m+1),j.val := by
  classical
  have h : (∑ j∈Finset.univ.map r,j.val)≤∑ j : Fin (m+1),j.val :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  simpa using h

theorem total_sum_le_selected_add_omitted {m k : ℕ} (r : Fin k ↪ Fin (m+1)) :
    (∑ j : Fin (m+1),j.val)≤(∑ i,(r i).val)+(m+1-k)*m := by
  classical
  let S := Finset.univ.map r
  have hS : S.card=k := by simp [S]
  have hpart := Finset.sum_sdiff (s₁:=S) (s₂:=Finset.univ) (f:=fun j : Fin (m+1) => j.val)
    (Finset.subset_univ _)
  have hcard : (Finset.univ\S).card=m+1-k := by rw [Finset.card_sdiff]; simp [hS]
  have hb : (∑ j∈Finset.univ\S,j.val)≤(m+1-k)*m := by
    calc
      _ ≤ ∑ j∈Finset.univ\S,m := Finset.sum_le_sum (fun j _ => by omega)
      _ = _ := by simp [hcard]
  have hsum : (∑ j∈S,j.val)=∑ i,(r i).val := by simp [S]
  rw [hsum] at hpart
  omega

theorem selected_sum_difference_bound {m k : ℕ} (r c : Fin k ↪ Fin (m+1)) :
    (∑ i,(c i).val)-(∑ i,(r i).val)≤(m+1-k)*m := by
  have h1 := selected_sum_le_total c
  have h2 := total_sum_le_selected_add_omitted r
  omega

theorem selected_sum_difference_four (m : ℕ)
    (r c : Fin (m+1-4) ↪ Fin (m+1)) :
    (∑ i,(c i).val)-(∑ i,(r i).val)≤4*m := by
  apply (selected_sum_difference_bound r c).trans
  exact Nat.mul_le_mul_right m (by omega)
end OddZeta.FourValue

import FourValueArithmeticLattice

namespace OddZeta.FourValue.ArithmeticBoxes

theorem half_open_cover {n : ℕ} (f : Fin (n+1) → ℚ) (x : ℚ)
 (hl : f 0<x) (hh : x≤f (Fin.last n)) :
 ∃ i : Fin n,f i.castSucc<x ∧ x≤f i.succ := by
 induction n with
 | zero => simp at hl hh; linarith
 | succ n ih =>
   by_cases hx : x≤f ⟨n,by omega⟩
   · obtain ⟨i,hi⟩ := ih (fun j => f j.castSucc) hl hx
     exact ⟨i.castSucc,hi⟩
   · exact ⟨Fin.last n,lt_of_not_ge hx,hh⟩

theorem open_or_boundary {n : ℕ} (f : Fin (n+1) → ℚ) (x : ℚ)
 (hl : f 0≤x) (hh : x≤f (Fin.last n)) :
 (∃j,x=f j) ∨ ∃i : Fin n,f i.castSucc<x ∧ x<f i.succ := by
 by_cases he : x=f 0
 · exact Or.inl ⟨0,he⟩
 · obtain ⟨i,hi⟩ := half_open_cover f x (lt_of_le_of_ne hl (Ne.symm he)) hh
   by_cases he' : x=f i.succ
   · exact Or.inl ⟨i.succ,he'⟩
   · exact Or.inr ⟨i,hi.1,lt_of_le_of_ne hi.2 he'⟩

end OddZeta.FourValue.ArithmeticBoxes

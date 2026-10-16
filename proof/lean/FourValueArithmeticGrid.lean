import FourValueCellValuation

noncomputable section
namespace OddZeta.FourValue.ArithmeticCertificate
open Finset

structure Grid where
 count : ℕ
 cut : Fin (count+1) → ℚ
 cell : Fin count → Cell

structure Grid.Valid (G : Grid) : Prop where
 count_eq : G.count=171504
 cut_zero : G.cut 0=1/20
 cut_last : G.cut (Fin.last G.count)=361
 cut_mono : StrictMono G.cut
 cells : ∀i,(G.cell i).lo=G.cut i.castSucc ∧ (G.cell i).hi=G.cut i.succ ∧ (G.cell i).Valid
 integral : -114800≤∑i,((G.cell i).hi-(G.cell i).lo)*(G.cell i).lower

def Grid.error (G : Grid) : ℚ := 1+∑i,|(G.cell i).error|
def Grid.step (G : Grid) (u : ℚ) : ℚ :=
 ∑i,if (G.cell i).lo<u ∧ u≤(G.cell i).hi then (G.cell i).lower else 0

theorem Grid.cover (G : Grid) (hG : G.Valid) (u : ℚ) (hu : 1/20<u ∧ u≤361) :
 ∃i,(G.cell i).lo<u ∧ u≤(G.cell i).hi := by
 obtain ⟨i,hi⟩ := ArithmeticBoxes.half_open_cover G.cut u
   (by simpa [hG.cut_zero] using hu.1) (by simpa [hG.cut_last] using hu.2)
 exact ⟨i,by simpa [(hG.cells i).1,(hG.cells i).2.1] using hi⟩

theorem Grid.unique (G : Grid) (hG : G.Valid) (u : ℚ) (i j : Fin G.count)
 (hi : (G.cell i).lo<u ∧ u≤(G.cell i).hi)
 (hj : (G.cell j).lo<u ∧ u≤(G.cell j).hi) : i=j := by
 have hloi := (hG.cells i).1
 have hhii := (hG.cells i).2.1
 have hloj := (hG.cells j).1
 have hhij := (hG.cells j).2.1
 by_contra he
 rcases lt_or_gt_of_ne he with hij | hji
 · have hh := hG.cut_mono.monotone (show i.succ ≤ j.castSucc by simpa using hij)
   rw [← hhii,← hloj] at hh
   linarith [hi.2,hj.1]
 · have hh := hG.cut_mono.monotone (show j.succ ≤ i.castSucc by simpa using hji)
   rw [← hhij,← hloi] at hh
   linarith [hj.2,hi.1]

theorem Grid.step_eq (G : Grid) (hG : G.Valid) (u : ℚ) (i : Fin G.count)
 (hi : (G.cell i).lo<u ∧ u≤(G.cell i).hi) : G.step u=(G.cell i).lower := by
 unfold Grid.step
 rw [sum_eq_single i]
 · simp [hi]
 · intro j _ hji
   have hh : ¬((G.cell j).lo<u ∧ u≤(G.cell j).hi) := fun hj => hji (G.unique hG u j i hj hi)
   simp [hh]
 · simp

theorem Grid.step_zero_small (G : Grid) (hG : G.Valid) (u : ℚ) (hu : u≤1/20) : G.step u=0 := by
 apply sum_eq_zero
 intro i _
 have hh := (hG.cells i).2.2.lo_pos
 have : ¬(G.cell i).lo<u := by linarith
 simp [this]

theorem Grid.error_ge (G : Grid) (i : Fin G.count) : (G.cell i).error≤G.error := by
 have hh := single_le_sum (s:=univ) (f:=fun j => |(G.cell j).error|) (fun _ _ => abs_nonneg _) (mem_univ i)
 unfold Grid.error
 linarith [le_abs_self (G.cell i).error]

end OddZeta.FourValue.ArithmeticCertificate

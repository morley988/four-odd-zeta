import FourValueBoundaryPenalty
import FourValueFiniteCutCover

noncomputable section
namespace OddZeta.FourValue.ArithmeticCertificate
open Finset Corrected
variable {p : ℕ} [Fact p.Prime]

def Cell.classPenalty (c : Cell) (n : ℕ) (r : Fin (p/2+1)) : ℤ :=
 (∑i,if (c.box i).lo<(r.val:ℚ)/n ∧ (r.val:ℚ)/n<(c.box i).hi then (c.box i).pen else 0)+
 if ∃j,(r.val:ℚ)/n=c.cut j then 1000000000000 else 0

theorem Cell.penalty_nonneg (c : Cell) (hc : c.Valid) (n : ℕ) (r : Fin (p/2+1)) :
 0≤c.classPenalty n r := by
 unfold Cell.classPenalty
 apply add_nonneg
 · apply sum_nonneg
   intro i _
   split_ifs
   · exact (hc.boxes i).2.2.penalty_nonneg
   · rfl
 · split_ifs <;> norm_num

theorem Cell.local_minorLower (c : Cell) (hc : c.Valid) (n : ℕ) (z : Fin 4 → ℚ)
 (hn : 0<n) (hx : c.lo<(p:ℚ)/n ∧ (p:ℚ)/n≤c.hi)
 (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator z)
 (r : Fin (p/2+1)) (d : ℕ) :
 Allocation.MinorLower (p:=p) (integralLocalMatrix n (67*n) (pairedPoles n r) z d)
 (fun m => c.price*m-c.classPenalty n r) := by
 have hnq : (0:ℚ)<n := by exact_mod_cast hn
 have hy0 : (0:ℚ)≤(r.val:ℚ)/n := by positivity
 have hy1 : (r.val:ℚ)/n≤c.hi/2 := by
   have hr : (r.val:ℚ)≤(p:ℚ)/2 := by
     have h:=r.isLt
     have hh:=Nat.div_mul_le_self p 2
     have hz : (2:ℚ)*r.val≤p := by exact_mod_cast (show 2*r.val≤p by omega)
     linarith
   have hh := div_le_div_of_nonneg_right hr hnq.le
   have he : ((p:ℚ)/2)/n=((p:ℚ)/n)/2 := by ring
   rw [he] at hh
   linarith [hx.2]
 have hcover := ArithmeticBoxes.open_or_boundary c.cut ((r.val:ℚ)/n)
   (by simpa [hc.cut_zero] using hy0) (by simpa [hc.cut_last] using hy1)
 have hn20 : n≤20*p := by
   have hh : (1:ℚ)/20≤(p:ℚ)/n := hc.lo_pos.trans hx.1.le
   have hh' := (le_div_iff₀ hnq).mp hh
   have : (n:ℚ)≤20*p := by linarith
   exact_mod_cast this
 have hsum : (0:ℤ)≤∑i,if (c.box i).lo<(r.val:ℚ)/n ∧ (r.val:ℚ)/n<(c.box i).hi then (c.box i).pen else 0 := by
   apply sum_nonneg
   intro i _
   split_ifs
   · exact (hc.boxes i).2.2.penalty_nonneg
   · rfl
 rcases hcover with hbd | ⟨i,hi⟩
 · intro m u v
   have hh := boundary_minorLower n z r hn20 hs hp c.price hc.price_abs d m u v
   apply hh.mono
   simp only [Cell.classPenalty,if_pos hbd]
   omega
 · have hbi := hc.boxes i
   have hmem : (c.box i).lo<(r.val:ℚ)/n ∧ (r.val:ℚ)/n<(c.box i).hi := by simpa [hbi.1,hbi.2.1] using hi
   have hh := (c.box i).local_minorLower hbi.2.2 n z r hn ⟨hx.1.le,hx.2⟩ hmem
     (c.normalization_lower hc n p hn hx) hs hp d
   have hsumi : (c.box i).pen≤∑j,if (c.box j).lo<(r.val:ℚ)/n ∧ (r.val:ℚ)/n<(c.box j).hi then (c.box j).pen else 0 := by
     have h := single_le_sum (s:=univ) (a:=i) (f:=fun j => if (c.box j).lo<(r.val:ℚ)/n ∧ (r.val:ℚ)/n<(c.box j).hi then (c.box j).pen else 0)
       (fun j _ => by split_ifs; exact (hc.boxes j).2.2.penalty_nonneg; rfl) (mem_univ i)
     simpa [hmem] using h
   intro m u v
   apply (hh m u v).mono
   change c.price*(m:ℤ)-c.classPenalty n r≤c.price*(m:ℤ)-(c.box i).pen
   unfold Cell.classPenalty
   split_ifs <;> omega
end OddZeta.FourValue.ArithmeticCertificate

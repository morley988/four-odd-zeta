import FourValueCellPenalty
import FourValueRationalLattice

noncomputable section
namespace OddZeta.FourValue.ArithmeticCertificate
open Finset

theorem scaled_fin_count {m : ℕ} (S : Finset (Fin m)) (a b N : ℚ)
 (hN : 0<N) (hab : a≤b) (hS : ∀r∈S,a≤(r.val:ℚ)/N ∧ (r.val:ℚ)/N≤b) :
 (S.card:ℚ)≤N*(b-a)+1 := by
 let f : Fin m → ℤ := fun r => r.val
 have hf : Function.Injective f := by
   intro r s h
   change (r.val:ℤ)=(s.val:ℤ) at h
   apply Fin.ext
   exact_mod_cast h
 have hh := RationalBoxes.scaled_integer_interval_count (S.image f) a b N hN hab (by
   intro z hz
   obtain ⟨r,hr,rfl⟩ := mem_image.mp hz
   simpa only [f,Int.cast_natCast] using hS r hr)
 simpa only [card_image_of_injective _ hf] using hh

def Cell.roundingPenalty (c : Cell) : ℤ :=
 1000000000000*(c.count+1)+∑i,(c.box i).pen

theorem Cell.boundary_count (c : Cell) (n p : ℕ) (hn : 0<n) :
 ((univ.filter (fun r : Fin (p/2+1) => ∃j,(r.val:ℚ)/n=c.cut j)).card)≤c.count+1 := by
 let S := univ.filter (fun r : Fin (p/2+1) => ∃j,(r.val:ℚ)/n=c.cut j)
 let f : Fin (p/2+1) → ℚ := fun r => (r.val:ℚ)/n
 have hnq : (n:ℚ)≠0 := by exact_mod_cast hn.ne'
 have hf : Function.Injective f := by
   intro r s h
   have he : (r.val:ℚ)=(s.val:ℚ) := (div_left_inj' hnq).mp h
   apply Fin.ext
   exact_mod_cast he
 have hsub : S.image f⊆univ.image c.cut := by
   intro y hy
   obtain ⟨r,hr,rfl⟩ := mem_image.mp hy
   obtain ⟨j,hj⟩ := (mem_filter.mp hr).2
   exact mem_image.mpr ⟨j,mem_univ _,hj.symm⟩
 change S.card≤_
 calc S.card=(S.image f).card := (card_image_of_injective S hf).symm
      _≤(univ.image c.cut).card := card_le_card hsub
      _≤c.count+1 := by simpa using (card_image_le (s:=univ) (f:=c.cut))

theorem Cell.penalty_sum_upper (c : Cell) (hc : c.Valid) (n p : ℕ) (hn : 0<n) :
 (∑r : Fin (p/2+1),(c.classPenalty n r:ℚ))≤
 (n:ℚ)*c.widthPenalty+c.roundingPenalty := by
 have hnq : (0:ℚ)<n := by exact_mod_cast hn
 let S : Fin c.count → Finset (Fin (p/2+1)) := fun i => univ.filter
   (fun r => (c.box i).lo<(r.val:ℚ)/n ∧ (r.val:ℚ)/n<(c.box i).hi)
 have hcount (i : Fin c.count) : ((S i).card:ℚ)≤n*((c.box i).hi-(c.box i).lo)+1 := by
   apply scaled_fin_count (S i) _ _ _ hnq (hc.boxes i).2.2.lt.le
   intro r hr
   exact ⟨((mem_filter.mp hr).2).1.le,((mem_filter.mp hr).2).2.le⟩
 have hsum := RationalBoxes.weighted_count_upper (fun i => (S i).card)
   (fun i => (c.box i).hi-(c.box i).lo) (fun i => ((c.box i).pen:ℚ)) (n:ℚ)
   (fun i => by exact_mod_cast (hc.boxes i).2.2.penalty_nonneg) hcount
 have hb : (((univ.filter (fun r : Fin (p/2+1) => ∃j,(r.val:ℚ)/n=c.cut j)).card):ℚ)≤c.count+1 := by
   exact_mod_cast c.boundary_count n p hn
 have he : (∑r : Fin (p/2+1),(c.classPenalty n r:ℚ))=
   (∑i,((S i).card:ℚ)*(c.box i).pen)+
   ((univ.filter (fun r : Fin (p/2+1) => ∃j,(r.val:ℚ)/n=c.cut j)).card:ℚ)*1000000000000 := by
   simp only [Cell.classPenalty,Int.cast_add,Int.cast_sum,Int.cast_ite,Int.cast_zero,
     Int.cast_ofNat,sum_add_distrib]
   rw [sum_comm]
   simp only [← sum_filter,sum_const,nsmul_eq_mul,S]
 unfold Cell.widthPenalty Cell.roundingPenalty
 rw [he]
 push_cast
 linarith
end OddZeta.FourValue.ArithmeticCertificate

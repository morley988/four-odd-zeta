import FourValueGlobalCosts
import FourValueArithmeticLattice

noncomputable section
namespace OddZeta.FourValue.Corrected
variable {p : ℕ} [Fact p.Prime]

/-- Upper bounds for the two endpoint floors locate every surviving pole. -/
theorem goodClass_of_floor_bounds (n : ℕ) (r : Fin (p/2+1)) (U V : ℤ)
 (hU : (63*(n:ℤ)+r.val)/(p:ℤ)≤U)
 (hV : (63*(n:ℤ)-r.val)/(p:ℤ)≤V)
 (hgU : 67*(n:ℤ)-r.val+(p:ℤ)*U<(p:ℤ))
 (hgV : 67*(n:ℤ)+r.val+(p:ℤ)*V<(p:ℤ)) : goodClass n r := by
 intro a ha
 obtain ⟨haw,har⟩ := mem_pairedPoles n r a ha
 simp only [poleWindow,Finset.mem_Icc,Nat.cast_mul,Nat.cast_ofNat] at haw
 have hp : 0<(p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
 have haR : 67*(n:ℤ)-a<(p:ℤ) := by
   rcases har with ⟨k,hk⟩ | ⟨k,hk⟩
   · have hkL : -k≤(63*(n:ℤ)+r.val)/(p:ℤ) :=
       (Int.le_ediv_iff_mul_le hp).mpr (by nlinarith)
     have hmul := mul_le_mul_of_nonneg_left (hkL.trans hU) hp.le
     nlinarith
   · have hkL : -k≤(63*(n:ℤ)-r.val)/(p:ℤ) :=
       (Int.le_ediv_iff_mul_le hp).mpr (by nlinarith)
     have hmul := mul_le_mul_of_nonneg_left (hkL.trans hV) hp.le
     nlinarith
 omega

theorem singleClass_of_floor_bounds (n : ℕ) (r : Fin (p/2+1)) (U V : ℤ)
 (hU : (63*(n:ℤ)+r.val)/(p:ℤ)≤U)
 (hV : (63*(n:ℤ)-r.val)/(p:ℤ)≤V) (hUV : U+V≤0) : singleClass n r := by
 intro a ha
 obtain ⟨haw,har⟩ := mem_pairedPoles n r a ha
 have he : centeredResidueCount p a (63*n)=centeredResidueCount p r.val (63*n) := by
   rcases har with hl | hr
   · exact centeredResidueCount_congr a r.val (63*n) hl
   · have h := centeredResidueCount_congr a (-r.val) (63*n) (by simpa using hr)
     simpa only [centeredResidueCount_neg] using h
 have hlo : 1≤centeredResidueCount p a (63*n) := by
   rw [centeredResidueCount_eq_card]
   have hm : a∈(poleWindow (63*n)).filter (fun t => (p:ℤ)∣a-t) := by simp [haw]
   have hc := Finset.card_pos.mpr ⟨a,hm⟩
   exact_mod_cast hc
 rw [he,centeredResidueCount_floor] at hlo ⊢
 push_cast at hlo ⊢
 omega

/-- A finite cost table transfers to all minors after the capacity bound is proved. -/
theorem minorLower_of_finite_box (n : ℕ) (lambda : Fin 4 → ℚ)
 (r : Fin (p/2+1)) (d cap : ℕ) (price pen : ℤ) (cost : ℕ → ℤ)
 (hcap : targetResidueCapacity p n r.val≤cap)
 (hcost : ∀m,m≤cap → price*m-pen≤cost m)
 (hloc : ∀m,∀u v : Fin m → Fin d,PadicLower p (cost m)
   ((integralLocalMatrix n (67*n) (pairedPoles n r) lambda d).submatrix u v).det) :
 Allocation.MinorLower (p:=p)
   (integralLocalMatrix n (67*n) (pairedPoles n r) lambda d) (fun m => price*m-pen) := by
 intro m u v
 by_cases hm : m≤cap
 · exact (hloc m u v).mono (hcost m hm)
 · apply Or.inl
   exact integralLocalMatrix_capacity n (67*n) (pairedPoles n r) r.val lambda u v
     (fun a ha => (mem_pairedPoles n r a ha).2) (by omega)

#print axioms goodClass_of_floor_bounds
#print axioms singleClass_of_floor_bounds
end OddZeta.FourValue.Corrected

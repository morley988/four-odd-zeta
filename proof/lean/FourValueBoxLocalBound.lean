import FourValueCellNormalization

noncomputable section
namespace OddZeta.FourValue.ArithmeticCertificate
open Finset Corrected
variable {p : ℕ} [Fact p.Prime]

theorem Box.good_class (B : Box) {l h : ℚ} {t norm : ℤ}
 (hv : B.Valid l h t norm) (n : ℕ) (r : Fin (p/2+1)) (hn : 0<n)
 (hx : l≤(p:ℚ)/n ∧ (p:ℚ)/n≤h) (hy : B.lo<(r.val:ℚ)/n ∧ (r.val:ℚ)/n<B.hi)
 (hg : B.good=true) : goodClass n r := by
 have hf := B.discrete_floors hv n r.val hn hx hy 2
 have h00 := hv.good_corners hg l (by simp) B.lo (by simp)
 have h01 := hv.good_corners hg l (by simp) B.hi (by simp)
 have h10 := hv.good_corners hg h (by simp) B.lo (by simp)
 have h11 := hv.good_corners hg h (by simp) B.hi (by simp)
 have hU := RationalBoxes.affine_rectangle_pos (1-(B.plusHi 2:ℚ)) 1 (-67)
   l h B.lo B.hi ((p:ℚ)/n) ((r.val:ℚ)/n) hx hy (by norm_num)
   (by linarith [h00.1]) (by linarith [h01.1]) (by linarith [h10.1]) (by linarith [h11.1])
 have hV := RationalBoxes.affine_rectangle_pos (1-(B.minusHi 2:ℚ)) (-1) (-67)
   l h B.lo B.hi ((p:ℚ)/n) ((r.val:ℚ)/n) hx hy (by norm_num)
   (by linarith [h00.2]) (by linarith [h01.2]) (by linarith [h10.2]) (by linarith [h11.2])
 have hnq : (0:ℚ)<n := by exact_mod_cast hn
 have hu := mul_pos hU hnq
 have hvv := mul_pos hV hnq
 field_simp [hnq.ne'] at hu hvv
 apply goodClass_of_floor_bounds n r (B.plusHi 2) (B.minusHi 2) hf.2.1 hf.2.2.2
 · have hh : (67:ℚ)*n-r.val+p*(B.plusHi 2:ℚ)<p := by nlinarith
   exact_mod_cast hh
 · have hh : (67:ℚ)*n+r.val+p*(B.minusHi 2:ℚ)<p := by nlinarith
   exact_mod_cast hh

theorem Box.local_minorLower (B : Box) {l h : ℚ} {t norm : ℤ}
 (hv : B.Valid l h t norm) (n : ℕ) (z : Fin 4 → ℚ) (r : Fin (p/2+1)) (hn : 0<n)
 (hx : l≤(p:ℚ)/n ∧ (p:ℚ)/n≤h) (hy : B.lo<(r.val:ℚ)/n ∧ (r.val:ℚ)/n<B.hi)
 (hnorm : norm≤targetNormalizationFloor p n)
 (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator z) (d : ℕ) :
 Allocation.MinorLower (p:=p) (integralLocalMatrix n (67*n) (pairedPoles n r) z d)
 (fun m => t*m-B.pen) := by
 apply minorLower_of_finite_box n z r d B.cap t B.pen B.cost
   (B.capacity_upper hv n r.val hn hx hy)
 · intro m hm
   exact hv.dual ⟨m,by omega⟩
 · intro m u v
   have hlam := B.lambda_lower hv n r.val hn hx hy hnorm
   have hnu := hv.normalization.trans hnorm
   have hm : (0:ℤ)≤m := by positivity
   unfold Box.cost
   split_ifs with hg ht
   · have hgood := B.good_class hv n r hn hx hy hg
     have hf := B.discrete_floors hv n r.val hn hx hy 2
     have hsingle := singleClass_of_floor_bounds n r (B.plusHi 2) (B.minusHi 2)
       hf.2.1 hf.2.2.2 (hv.single_count ht)
     apply (integralLocalMatrix_single n (67*n) (pairedPoles n r) r.val z u v hs hp
       (fun a ha => ⟨(mem_pairedPoles n r a ha).1,hsingle a ha,
         (mem_pairedPoles n r a ha).2,hgood a ha⟩)).mono
     apply max_le_max <;> nlinarith
   · have hgood := B.good_class hv n r hn hx hy hg
     apply (integralLocalMatrix_good n (67*n) (pairedPoles n r) r.val z u v hs hp
       (fun a ha => ⟨(pairedPoles_small n r hs a ha).1,(mem_pairedPoles n r a ha).2,hgood a ha⟩)).mono
     nlinarith
   · apply (integralLocalMatrix_bad n (67*n) (pairedPoles n r) r.val z u v hs hp
       (pairedPoles_small n r hs)).mono
     nlinarith
end OddZeta.FourValue.ArithmeticCertificate

import FourValueArithmeticCertificate
import FourValueClassBoxBridge

noncomputable section
namespace OddZeta.FourValue.ArithmeticCertificate
open Finset

theorem Box.floor_bounds (B : Box) {l h : ℚ} {t norm : ℤ}
 (hv : B.Valid l h t norm) (u y : ℚ) (hu : 0<u)
 (hx : l≤u ∧ u≤h) (hy : B.lo<y ∧ y<B.hi) (i : Fin 12) :
 B.plusLo i≤⌊((allA i:ℚ)+y)/u⌋ ∧ ⌊((allA i:ℚ)+y)/u⌋≤B.plusHi i ∧
 B.minusLo i≤⌊((allA i:ℚ)-y)/u⌋ ∧ ⌊((allA i:ℚ)-y)/u⌋≤B.minusHi i := by
 have h00 := hv.floors i l (by simp) B.lo (by simp)
 have h01 := hv.floors i l (by simp) B.hi (by simp)
 have h10 := hv.floors i h (by simp) B.lo (by simp)
 have h11 := hv.floors i h (by simp) B.hi (by simp)
 have hp := RationalBoxes.floor_ratio_rectangle (allA i) 1 l h B.lo B.hi u y
   (B.plusLo i) (B.plusHi i) hu hx hy (by norm_num)
   (by simpa using h00.1) (by simpa using h01.1) (by simpa using h10.1) (by simpa using h11.1)
   (by simpa using h00.2.1) (by simpa using h01.2.1) (by simpa using h10.2.1) (by simpa using h11.2.1)
 have hm := RationalBoxes.floor_ratio_rectangle (allA i) (-1) l h B.lo B.hi u y
   (B.minusLo i) (B.minusHi i) hu hx hy (by norm_num)
   (by nlinarith [h00.2.2.1]) (by nlinarith [h01.2.2.1]) (by nlinarith [h10.2.2.1]) (by nlinarith [h11.2.2.1])
   (by simpa using h00.2.2.2) (by simpa using h01.2.2.2) (by simpa using h10.2.2.2) (by simpa using h11.2.2.2)
 simpa [sub_eq_add_neg] using And.intro hp.1 (And.intro hp.2 hm)

theorem scaled_floor (a : ℕ) (r : ℤ) (n p : ℕ) (hn : 0<n) :
 ⌊((a:ℚ)+(r:ℚ)/(n:ℚ))/((p:ℚ)/(n:ℚ))⌋=((a:ℤ)*n+r)/(p:ℤ) := by
 have hnq : (n:ℚ)≠0 := by exact_mod_cast hn.ne'
 have he : ((a:ℚ)+(r:ℚ)/(n:ℚ))/((p:ℚ)/(n:ℚ))=
   (((a:ℤ)*n+r:ℤ):ℚ)/(p:ℚ) := by push_cast; field_simp <;> ring
 rw [he,Rat.floor_intCast_div_natCast]

variable {p : ℕ} [Fact p.Prime]

theorem Box.discrete_floors (B : Box) {l h : ℚ} {t norm : ℤ}
 (hv : B.Valid l h t norm) (n : ℕ) (r : ℤ) (hn : 0<n)
 (hx : l≤(p:ℚ)/n ∧ (p:ℚ)/n≤h) (hy : B.lo<(r:ℚ)/n ∧ (r:ℚ)/n<B.hi) (i : Fin 12) :
 B.plusLo i≤((allA i:ℤ)*n+r)/(p:ℤ) ∧ ((allA i:ℤ)*n+r)/(p:ℤ)≤B.plusHi i ∧
 B.minusLo i≤((allA i:ℤ)*n-r)/(p:ℤ) ∧ ((allA i:ℤ)*n-r)/(p:ℤ)≤B.minusHi i := by
 have hpq : (0:ℚ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
 have hnq : (0:ℚ)<n := by exact_mod_cast hn
 have hh := B.floor_bounds hv (p/n) (r/n) (div_pos hpq hnq) hx hy i
 rw [scaled_floor _ _ _ _ hn] at hh
 have he : ((allA i:ℚ)-(r:ℚ)/n)/(p/n)=((allA i:ℚ)+((-r:ℤ):ℚ)/n)/(p/n) := by push_cast; ring
 rw [he,scaled_floor _ _ _ _ hn] at hh
 simpa only [sub_eq_add_neg] using hh

end OddZeta.FourValue.ArithmeticCertificate

namespace OddZeta.FourValue.ArithmeticCertificate
open Finset
variable {p : ℕ} [Fact p.Prime]

theorem Box.count_bounds (B : Box) {l h : ℚ} {t norm : ℤ}
 (hv : B.Valid l h t norm) (n : ℕ) (r : ℤ) (hn : 0<n)
 (hx : l≤(p:ℚ)/n ∧ (p:ℚ)/n≤h) (hy : B.lo<(r:ℚ)/n ∧ (r:ℚ)/n<B.hi) (i : Fin 12) :
 B.lowerCount i≤centeredResidueCount p r (allA i*n) ∧
 centeredResidueCount p r (allA i*n)≤B.upperCount i := by
 have hh := B.discrete_floors hv n r hn hx hy i
 rw [centeredResidueCount_floor]
 simp only [Nat.cast_mul]
 unfold Box.lowerCount Box.upperCount
 omega

theorem Box.capacity_upper (B : Box) {l h : ℚ} {t norm : ℤ}
 (hv : B.Valid l h t norm) (n : ℕ) (r : ℤ) (hn : 0<n)
 (hx : l≤(p:ℚ)/n ∧ (p:ℚ)/n≤h) (hy : B.lo<(r:ℚ)/n ∧ (r:ℚ)/n<B.hi) :
 targetResidueCapacity p n r≤B.cap := by
 have hh (i : Fin 10) : centeredResidueCount p r (targetFactorialEndpoints i*n)≤
   B.upperCount ⟨i.val+2,by omega⟩ := by
   have he : allA ⟨i.val+2,by omega⟩=targetFactorialEndpoints i := by fin_cases i <;> rfl
   simpa only [he] using (B.count_bounds hv n r hn hx hy ⟨i.val+2,by omega⟩).2
 have hs := (sum_le_sum (s:=univ) (fun i _ => hh i)).trans hv.capacity
 rw [← targetResidueCapacity_count] at hs
 exact_mod_cast hs

theorem targetLocalWeight_split (n : ℕ) (r : ℤ) :
 targetLocalWeight p n r=targetNormalizationFloor p n+rootResidueWeight p r+
 5*centeredResidueCount p r (100*n)-5*centeredResidueCount p r (67*n)-
 ∑i : Fin 10,centeredResidueCount p r (targetFactorialEndpoints i*n) := by
 simp [targetLocalWeight,targetEndpointTuple,targetFactorialEndpoints,Fin.sum_univ_succ]
 <;> ring

theorem Box.lambda_lower (B : Box) {l h : ℚ} {t norm : ℤ}
 (hv : B.Valid l h t norm) (n : ℕ) (r : ℤ) (hn : 0<n)
 (hx : l≤(p:ℚ)/n ∧ (p:ℚ)/n≤h) (hy : B.lo<(r:ℚ)/n ∧ (r:ℚ)/n<B.hi)
 (hnorm : norm≤targetNormalizationFloor p n) : B.lam≤targetLocalWeight p n r := by
 have h100 := (B.count_bounds hv n r hn hx hy 0).1
 have h67 := (B.count_bounds hv n r hn hx hy 1).2
 change B.lowerCount 0≤centeredResidueCount p r (100*n) at h100
 change centeredResidueCount p r (67*n)≤B.upperCount 1 at h67
 have hh (i : Fin 10) : centeredResidueCount p r (targetFactorialEndpoints i*n)≤B.upperCount ⟨i.val+2,by omega⟩ := by
   have he : allA ⟨i.val+2,by omega⟩=targetFactorialEndpoints i := by fin_cases i <;> rfl
   simpa only [he] using (B.count_bounds hv n r hn hx hy ⟨i.val+2,by omega⟩).2
 have hs := sum_le_sum (s:=univ) (fun i _ => hh i)
 have hr := (rootResidueWeight_bounds (p:=p) r).1
 rw [targetLocalWeight_split]
 have hl := hv.lambda
 linarith

end OddZeta.FourValue.ArithmeticCertificate

import FourValueBoxLocalBound

noncomputable section
namespace OddZeta.FourValue.Corrected
open Finset
variable {p : ℕ} [Fact p.Prime]

theorem centered_count_coarse (n b : ℕ) (r : Fin (p/2+1))
 (hn : n≤20*p) (hb : b≤100*n) : centeredResidueCount p r.val b≤4002 := by
 rw [centeredResidueCount_floor]
 have hp : (0:ℤ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
 have hr : r.val≤p := by have := r.isLt; omega
 have hb' : (b:ℤ)≤2000*(p:ℤ) := by exact_mod_cast (show b≤2000*p by omega)
 have hr' : (r.val:ℤ)≤p := by exact_mod_cast hr
 have h1 : ((b:ℤ)+r.val)/(p:ℤ)≤2001 := by
   have hh := (Int.ediv_lt_iff_lt_mul hp).mpr (show (b:ℤ)+r.val<2002*(p:ℤ) by nlinarith)
   omega
 have h2 : ((b:ℤ)-r.val)/(p:ℤ)≤2000 := by
   have hh := (Int.ediv_lt_iff_lt_mul hp).mpr (show (b:ℤ)-r.val<2001*(p:ℤ) by nlinarith)
   omega
 omega

theorem local_weight_coarse (n : ℕ) (r : Fin (p/2+1)) (hn : n≤20*p) :
 -100000≤targetLocalWeight p n r.val := by
 have hp : 0<p := (Fact.out : p.Prime).pos
 have h33 : 33*n/p≤660 := by
   have hh : 33*n/p<661 := (Nat.div_lt_iff_lt_mul hp).mpr (by nlinarith)
   omega
 have hnorm : -6600≤targetNormalizationFloor p n := by
   unfold targetNormalizationFloor
   have hh : (0:ℤ)≤∑i : Fin 10,((2*targetFactorialEndpoints i*n/p:ℕ):ℤ) :=
     sum_nonneg (fun i _ => by positivity)
   omega
 have hc := centeredResidueCount_nonneg (p:=p) r.val (100*n)
 have hr := (rootResidueWeight_bounds (p:=p) r.val).1
 have hs : (∑i : Fin 15,centeredResidueCount p r.val (targetEndpointTuple n i))≤15*4002 := by
   calc _≤∑i : Fin 15,(4002:ℤ) := sum_le_sum (fun i _ => centered_count_coarse n _ r hn
     ((targetEndpointTuple_le_67 n i).trans (by omega)))
        _=_ := by norm_num
 unfold targetLocalWeight
 linarith

theorem residue_capacity_coarse (n : ℕ) (r : Fin (p/2+1)) (hn : n≤20*p) :
 targetResidueCapacity p n r.val≤40020 := by
 have hh : (targetResidueCapacity p n r.val:ℤ)≤40020 := by
   rw [targetResidueCapacity_count]
   calc _≤∑i : Fin 10,(4002:ℤ) := sum_le_sum (fun i _ => centered_count_coarse n _ r hn (by
     have := targetFactorialEndpoints_le i
     nlinarith))
        _=_ := by norm_num
 exact_mod_cast hh

theorem boundary_minorLower (n : ℕ) (z : Fin 4 → ℚ) (r : Fin (p/2+1))
 (hn : n≤20*p) (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator z)
 (price : ℤ) (ht : |price|≤20000) (d : ℕ) :
 Allocation.MinorLower (p:=p) (integralLocalMatrix n (67*n) (pairedPoles n r) z d)
 (fun m => price*m-1000000000000) := by
 apply minorLower_of_finite_box n z r d 40020 price 1000000000000
   (fun m => (m:ℤ)^2+(-100005)*(m:ℤ)) (residue_capacity_coarse n r hn)
 · intro m hm
   have hmz : (m:ℤ)≤40020 := by exact_mod_cast hm
   have ht' := (abs_le.mp ht).2
   have hm0 : (0:ℤ)≤m := by positivity
   nlinarith [mul_le_mul_of_nonneg_right ht' hm0,sq_nonneg (m:ℤ)]
 · intro m u v
   apply (integralLocalMatrix_bad n (67*n) (pairedPoles n r) r.val z u v hs hp
     (pairedPoles_small n r hs)).mono
   have hw := local_weight_coarse n r hn
   have hm0 : (0:ℤ)≤m := by positivity
   nlinarith
end OddZeta.FourValue.Corrected

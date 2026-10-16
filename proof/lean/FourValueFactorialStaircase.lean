import FourValueCellRounding

noncomputable section
namespace OddZeta.FourValue.ArithmeticCertificate
open Finset
variable {p : ℕ} [Fact p.Prime]

theorem floor_staircase (a p K : ℕ) (hp : 0<p) (ha : a/p≤K) :
 ((a/p:ℕ):ℚ)=∑j∈range K,if (j+1)*p≤a then (1:ℚ) else 0 := by
 have he : (range K).filter (fun j => (j+1)*p≤a)=range (a/p) := by
   ext j
   simp only [mem_filter,mem_range,← Nat.le_div_iff_mul_le hp]
   omega
 rw [← sum_filter,he]
 simp

theorem sum_succ_rat (K : ℕ) : (∑j∈range K,((j:ℚ)+1))=(K:ℚ)*(K+1)/2 := by
 induction K with
 | zero => simp
 | succ K ih => rw [sum_range_succ,ih]; push_cast; ring

theorem factorial_staircase_upper (n : ℕ) (l : ℚ) (K : ℕ)
 (hn : 0<n) (hl : 0<l) (hu : l<(p:ℚ)/n)
 (hK : l*K≤361 ∧ 361≤l*(K+1)) :
 (∑i : Fin (targetHankelDegree n+1),((2*i.val/p:ℕ):ℚ))≤
 (n:ℚ)*(361*K-l*K*(K+1)/2)/2+K := by
 have hnq : (0:ℚ)<n := by exact_mod_cast hn
 have hp := (Fact.out : p.Prime).pos
 have hpn : l*(n:ℚ)<p := (lt_div_iff₀ hnq).mp hu
 have hi (i : Fin (targetHankelDegree n+1)) : 2*i.val≤361*n := by
   have hh:=i.isLt
   unfold targetHankelDegree at hh
   have hd := Nat.div_mul_le_self (361*n) 2
   omega
 have hfloor (i : Fin (targetHankelDegree n+1)) : 2*i.val/p≤K := by
   have h1 : (2:ℚ)*i.val≤361*n := by exact_mod_cast hi i
   have h2 : (2:ℚ)*i.val<(K+1)*p := by
     have hk : (0:ℚ)<K+1 := by positivity
     have hh:=mul_lt_mul_of_pos_left hpn hk
     have hg:=mul_le_mul_of_nonneg_right hK.2 hnq.le
     nlinarith
   have hz : 2*i.val<(K+1)*p := by exact_mod_cast h2
   have hh := (Nat.div_lt_iff_lt_mul hp).mpr hz
   omega
 simp_rw [floor_staircase _ _ K hp (hfloor _)]
 rw [sum_comm]
 have hcounts (j : ℕ) (hj : j∈range K) :
 (∑i : Fin (targetHankelDegree n+1),if (j+1)*p≤2*i.val then (1:ℚ) else 0)≤
 (n:ℚ)*(361-l*(j+1))/2+1 := by
   let S := univ.filter (fun i : Fin (targetHankelDegree n+1) => (j+1)*p≤2*i.val)
   have hjK : (j:ℚ)+1≤K := by exact_mod_cast (show j+1≤K by have hh := mem_range.mp hj; omega)
   have hja : l*((j:ℚ)+1)≤361 := (mul_le_mul_of_nonneg_left hjK hl.le).trans hK.1
   have hcount := scaled_fin_count S (l*n*(j+1)/2) (361*(n:ℚ)/2) 1 (by norm_num)
     (by nlinarith) (by
       intro i hiS
       have h1 : ((j:ℚ)+1)*p≤2*i.val := by exact_mod_cast (mem_filter.mp hiS).2
       have h2 : (2:ℚ)*i.val≤361*n := by exact_mod_cast hi i
       have h3:=mul_le_mul_of_nonneg_left hpn.le (show (0:ℚ)≤j+1 by positivity)
       constructor <;> simp only [div_one] <;> nlinarith)
   have he : (∑i : Fin (targetHankelDegree n+1),if (j+1)*p≤2*i.val then (1:ℚ) else 0)=(S.card:ℚ) := by
     simp only [← sum_filter,sum_const,nsmul_eq_mul,mul_one,S]
   rw [he]
   nlinarith
 have hh:=sum_le_sum hcounts
 have hsumid : (∑j∈range K,(j:ℚ))=(K:ℚ)*(K+1)/2-K := by
   have hh := sum_succ_rat K
   simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,mul_one] at hh
   linarith
 have he : (∑j∈range K,((n:ℚ)*(361-l*(j+1))/2+1))=
   (n:ℚ)*(361*K-l*K*(K+1)/2)/2+K := by
   simp only [sum_add_distrib,← sum_div,← mul_sum,sum_sub_distrib,sum_const,card_range,
     nsmul_eq_mul,hsumid]
   push_cast
   ring
 exact hh.trans_eq he

theorem selected_factorial_upper (n : ℕ) (l : ℚ) (K : ℕ)
 (hn : 0<n) (hl : 0<l) (hu : l<(p:ℚ)/n) (hK : l*K≤361 ∧ 361≤l*(K+1))
 (hs : 800*n<p^2) {k : ℕ}
 (rows cols : Fin k ↪ Fin (targetHankelDegree n+1)) :
 (selectedFactorialCost p n rows cols:ℚ)≤
 (n:ℚ)*(361*K-l*K*(K+1)/2)+2*K := by
 have hval (i : Fin (targetHankelDegree n+1)) : padicValNat p (2*i.val).factorial=2*i.val/p := by
   apply OddZeta.Coefficients.factorial_valuation_below_square
   have hi:=i.isLt
   unfold targetHankelDegree at hi
   have hd:=Nat.div_mul_le_self (361*n) 2
   omega
 have hinj (r : Fin k ↪ Fin (targetHankelDegree n+1)) :
 (∑i,((2*(r i).val/p:ℕ):ℚ))≤∑i : Fin (targetHankelDegree n+1),((2*i.val/p:ℕ):ℚ) := by
   calc _=∑i∈univ.map r,((2*i.val/p:ℕ):ℚ) := by simp
        _≤_ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
 have hf := factorial_staircase_upper n l K hn hl hu hK
 unfold selectedFactorialCost
 simp only [hval,Int.cast_add,Int.cast_sum,Int.cast_natCast]
 linarith [hinj rows,hinj cols]
end OddZeta.FourValue.ArithmeticCertificate

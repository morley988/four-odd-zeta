import FourValueScaledLaurent

noncomputable section
namespace OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

theorem truncatedRootValuation_sum (B : ℕ) (z : ℤ)
    (hv : padicValNat p z.natAbs≤B) :
    truncatedRootValuation p B z = ∑ e∈Finset.Ico 1 (B+1),rootResidueWeight (p^e) z := by
  by_cases hz : z=0
  · simp [hz,truncatedRootValuation,rootResidueWeight]
  unfold truncatedRootValuation
  rw [if_neg hz]
  have he : (Finset.Ico 1 (B+1)).filter (fun e => p^e∣z.natAbs) =
      Finset.Ico 1 (padicValNat p z.natAbs+1) := by
    ext e
    simp only [Finset.mem_filter,Finset.mem_Ico,padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hz)]
    omega
  simp only [rootResidueWeight,← Finset.sum_filter]
  rw [he]
  simp

theorem truncatedRootValuation_le_log (M B : ℕ) (z : ℤ)
    (hz : z.natAbs≤M) (hB : Nat.log p M≤B) : truncatedRootValuation p B z≤B := by
  unfold truncatedRootValuation
  split_ifs
  · omega
  have h := (padicValNat_le_nat_log z.natAbs).trans ((Nat.log_mono_right hz).trans hB)
  exact_mod_cast h

theorem centeredResidueCount_floor_modulus (q : ℕ) (hq : 0<q) (a : ℤ) (b : ℕ) :
    centeredResidueCount q a b = ((b:ℤ)+a)/(q:ℤ)+((b:ℤ)-a)/(q:ℤ)+1 := by
  have hp : 0<(q:ℤ) := by exact_mod_cast hq
  have hcard : centeredResidueCount q a b =
      (((poleWindow b).filter (fun t => (q:ℤ)∣a-t)).card:ℤ) := by
    simp [centeredResidueCount,rootResidueWeight,← Int.natCast_dvd,Finset.sum_boole]
  rw [hcard]
  have he : (poleWindow b).filter (fun t => (q:ℤ)∣a-t) =
      (Finset.Ioc (-(b:ℤ)-1) (b:ℤ)).filter (fun t => t ≡ a [ZMOD (q:ℤ)]) := by
    ext t
    simp only [Finset.mem_filter,poleWindow,Finset.mem_Icc,Finset.mem_Ioc,Int.modEq_iff_dvd]
    omega
  rw [he,Int.Ioc_filter_modEq_card _ _ hp]
  have hf (x : ℤ) : ⌊(x:ℚ)/(q:ℚ)⌋=x/(q:ℤ) := Rat.floor_intCast_div_natCast x q
  have he1 : (((b:ℤ):ℚ)-(a:ℚ))/(q:ℚ)=(((b:ℤ)-a:ℤ):ℚ)/(q:ℚ) := by push_cast; rfl
  have he2 : (((-(b:ℤ)-1):ℚ)-(a:ℚ))/(q:ℚ)=(((-(b:ℤ)-1-a:ℤ):ℚ))/(q:ℚ) := by push_cast; ring
  simp only [Int.cast_natCast] at he1 he2
  simp only [Int.cast_sub,Int.cast_neg,Int.cast_natCast,Int.cast_one]
  rw [he1,he2,hf,hf]
  have hn : 0≤((b:ℤ)-a)/(q:ℤ)-(-(b:ℤ)-1-a)/(q:ℤ) := by
    have h := Int.ediv_le_ediv hp (show -(b:ℤ)-1-a≤(b:ℤ)-a by omega)
    omega
  rw [max_eq_left hn]
  have hd : (-(b:ℤ)-1-a)/(q:ℤ) = -(((b:ℤ)+a)/(q:ℤ))-1 := by
    apply (Int.ediv_eq_iff_of_pos hp).mpr
    have h1 := Int.ediv_mul_le ((b:ℤ)+a) hp.ne'
    have h2 := Int.lt_ediv_add_one_mul_self ((b:ℤ)+a) hp
    constructor <;> nlinarith
  rw [hd]
  ring

theorem centeredResidueCount_scaled_bounds (q : ℕ) (hq : 0<q) (a : ℤ) (b : ℕ) :
    2*(b:ℤ)-(q:ℤ) ≤ (q:ℤ)*centeredResidueCount q a b ∧
    (q:ℤ)*centeredResidueCount q a b ≤ 2*(b:ℤ)+(q:ℤ) := by
  rw [centeredResidueCount_floor_modulus q hq]
  have hp : 0<(q:ℤ) := by exact_mod_cast hq
  have h1 := Int.ediv_mul_le ((b:ℤ)+a) hp.ne'
  have h2 := Int.lt_ediv_add_one_mul_self ((b:ℤ)+a) hp
  have h3 := Int.ediv_mul_le ((b:ℤ)-a) hp.ne'
  have h4 := Int.lt_ediv_add_one_mul_self ((b:ℤ)-a) hp
  constructor <;> nlinarith

theorem targetNormalizationValuation_sum (n M : ℕ) (hM : 126*n≤M) :
    targetNormalizationValuation p n =
      ∑ e∈Finset.Ico 1 (Nat.log p M+1),targetNormalizationFloor (p^e) n := by
  have hf (m : ℕ) (hm : m≤M) : (padicValNat p m.factorial:ℤ) =
      ∑ e∈Finset.Ico 1 (Nat.log p M+1),((m/p^e:ℕ):ℤ) := by
    rw [padicValNat_factorial (b:=Nat.log p M+1) (by have h := Nat.log_mono_right (b:=p) hm; omega)]
    push_cast
    rfl
  unfold targetNormalizationValuation targetNormalizationFloor
  have hh (i : Fin 10) := hf (2*targetFactorialEndpoints i*n) (by have hi := targetFactorialEndpoints_le i; nlinarith)
  simp_rw [hh]
  rw [hf (33*n) (by omega)]
  rw [Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  exact Finset.sum_comm
end OddZeta.FourValue

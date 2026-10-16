import FourValuePrimePowerCounts

noncomputable section
namespace OddZeta.FourValue
open Polynomial
open scoped RatFunc
variable {p : ℕ} [Fact p.Prime]

def truncatedCenteredCount (p B : ℕ) (a : ℤ) (b : ℕ) : ℤ :=
  ∑ t∈poleWindow b,truncatedRootValuation p B (a-t)

theorem truncatedCenteredCount_sum (B M : ℕ) (a : ℤ) (b : ℕ)
    (hM : ∀ t∈poleWindow b,(a-t).natAbs≤M) (hB : Nat.log p M≤B) :
    truncatedCenteredCount p B a b =
      ∑ e∈Finset.Ico 1 (B+1),centeredResidueCount (p^e) a b := by
  unfold truncatedCenteredCount centeredResidueCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  exact truncatedRootValuation_sum B _
    ((padicValNat_le_nat_log _).trans ((Nat.log_mono_right (hM t ht)).trans hB))

theorem centeredDenominator_scaledLaurent (B : ℕ) (a u : ℤ) (b : ℕ)
    (hw : ∀ t∈poleWindow b,truncatedRootValuation p B (u*a-t)≤B) :
    ScaledLaurentPadicLower p (a:ℚ) B (truncatedCenteredCount p B (u*a) b)
      (algebraMap ℚ[X] (RatFunc ℚ) ((centeredDenominator b).comp (C (u:ℚ)*X))) := by
  rw [centeredDenominator_integerProduct]
  simp only [integerRootProduct,prod_comp,sub_comp,X_comp,C_comp,map_prod]
  exact ScaledLaurentPadicLower.prod _ _ _ _ _ (fun t ht => scaledLinearFactor_laurent B a t u (hw t ht))

theorem inverseCenteredDenominator_scaledLaurent (B : ℕ) (a : ℤ) (b : ℕ)
    (hw : ∀ t∈poleWindow b,truncatedRootValuation p B (a-t)≤B) :
    ScaledLaurentPadicLower p (a:ℚ) B (-truncatedCenteredCount p B a b)
      ((algebraMap ℚ[X] (RatFunc ℚ) (centeredDenominator b))⁻¹) := by
  rw [centeredDenominator_integerProduct]
  simp only [integerRootProduct,map_prod,Finset.prod_inv_distrib]
  have h := ScaledLaurentPadicLower.prod (p:=p) (poleWindow b) (a:ℚ) B
    (fun t => -truncatedRootValuation p B (a-t)) (fun t => rationalPole (t:ℚ) 1)
    (fun t ht => inverseLinearFactor_scaledLaurent B a t (hw t ht))
  simpa [rationalPole,truncatedCenteredCount,Finset.sum_neg_distrib] using h

theorem targetNormalizationFloor_scaled_lower (q n : ℕ) (hq : 0<q) :
    722*(n:ℤ)-10*q ≤ (q:ℤ)*targetNormalizationFloor q n := by
  have hp : 0<(q:ℤ) := by exact_mod_cast hq
  have hn (i : Fin 10) : (2*targetFactorialEndpoints i*n:ℕ)-(q:ℤ) ≤
      (q:ℤ)*((2*targetFactorialEndpoints i*n/q:ℕ):ℤ) := by
    have h := Nat.div_add_mod (2*targetFactorialEndpoints i*n) q
    have hh := Nat.mod_lt (2*targetFactorialEndpoints i*n) hq
    have hh' : ((2*targetFactorialEndpoints i*n:ℕ):ℤ) =
      (q:ℤ)*((2*targetFactorialEndpoints i*n/q:ℕ):ℤ)+((2*targetFactorialEndpoints i*n%q:ℕ):ℤ) := by
      exact_mod_cast h.symm
    have hh'' : ((2*targetFactorialEndpoints i*n%q:ℕ):ℤ)<q := by exact_mod_cast hh
    omega
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i hi => hn i)
  have hd : (q:ℤ)*((33*n/q:ℕ):ℤ)≤33*n := by exact_mod_cast Nat.mul_div_le (33*n) q
  norm_num [Fin.sum_univ_succ,targetFactorialEndpoints] at hs
  unfold targetNormalizationFloor
  rw [mul_sub,Finset.mul_sum]
  have hsum : (∑ i : Fin 10, (q:ℤ)*((2*targetFactorialEndpoints i*n/q:ℕ):ℤ)) ≥
      1052*(n:ℤ)-10*q := by
    simp [Fin.sum_univ_succ,targetFactorialEndpoints]
    linarith [hs]
  nlinarith

theorem targetPrimePowerWeight_lower (q n : ℕ) (hq : 0<q) (a : ℤ) :
    -30 ≤ targetNormalizationFloor q n +5*centeredResidueCount q a (100*n)-
      ∑ i : Fin 15,centeredResidueCount q a (targetEndpointTuple n i) := by
  have hp : 0<(q:ℤ) := by exact_mod_cast hq
  have hN := targetNormalizationFloor_scaled_lower q n hq
  have hU := (centeredResidueCount_scaled_bounds q hq a (100*n)).1
  have hD := Finset.sum_le_sum (s:=Finset.univ)
    (fun (i : Fin 15) hi => (centeredResidueCount_scaled_bounds q hq a (targetEndpointTuple n i)).2)
  have hsum : (∑ i : Fin 15, (2*(targetEndpointTuple n i:ℤ)+(q:ℤ)))=1722*n+15*q := by
    simp [Fin.sum_univ_succ,targetEndpointTuple]
    ring
  rw [hsum,← Finset.mul_sum] at hD
  push_cast at hU
  nlinarith

theorem root_difference_le (M : ℕ) (a t : ℤ) (ha : a∈poleWindow M) (ht : t∈poleWindow M) :
    (a-t).natAbs≤2*M := by
  simp only [poleWindow,Finset.mem_Icc] at ha ht
  have h : |a-t|≤(2*M:ℕ) := by rw [abs_le]; push_cast; constructor <;> omega
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

def targetAllPrimeWeight (p n : ℕ) (a : ℤ) : ℤ :=
  targetNormalizationValuation p n+truncatedRootValuation p (Nat.log p (800*n)) a+
    5*truncatedCenteredCount p (Nat.log p (800*n)) a (100*n)-
    ∑ i : Fin 15,truncatedCenteredCount p (Nat.log p (800*n)) a (targetEndpointTuple n i)

theorem targetAllPrimeWeight_lower (n : ℕ) (a : ℤ) (ha : a∈poleWindow (100*n)) :
    -30*(Nat.log p (800*n):ℤ)≤targetAllPrimeWeight p n a := by
  have hwin (b : ℕ) (hb : b≤100*n) (t : ℤ) (ht : t∈poleWindow b) :
      (a-t).natAbs≤800*n := by
    apply (root_difference_le (100*n) a t ha ?_).trans (by omega)
    simp only [poleWindow,Finset.mem_Icc] at ht ⊢
    omega
  have hroot : 0≤truncatedRootValuation p (Nat.log p (800*n)) a := by
    unfold truncatedRootValuation
    split_ifs <;> omega
  unfold targetAllPrimeWeight
  rw [targetNormalizationValuation_sum n (800*n) (by omega),
    truncatedCenteredCount_sum _ (800*n) a (100*n) (hwin _ le_rfl) le_rfl]
  have hD : (∑ i : Fin 15,truncatedCenteredCount p (Nat.log p (800*n)) a (targetEndpointTuple n i)) =
      ∑ e∈Finset.Ico 1 (Nat.log p (800*n)+1),
        ∑ i : Fin 15,centeredResidueCount (p^e) a (targetEndpointTuple n i) := by
    simp_rw [truncatedCenteredCount_sum _ (800*n) a _
      (hwin _ (le_trans (targetEndpointTuple_le_67 n _) (by omega))) le_rfl]
    exact Finset.sum_comm
  rw [hD]
  have hs := Finset.sum_le_sum (s:=Finset.Ico 1 (Nat.log p (800*n)+1))
    (fun e he => targetPrimePowerWeight_lower (p^e) n (pow_pos (Fact.out : p.Prime).pos _) a)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum] at hs
  simp only [Finset.sum_const,Nat.card_Ico,Nat.add_sub_cancel,nsmul_eq_mul] at hs
  linarith

theorem targetNormalizedWeight_scaledLaurent (n : ℕ) (a : ℤ)
    (ha : a∈poleWindow (100*n)) :
    ScaledLaurentPadicLower p (a:ℚ) (Nat.log p (800*n)) (targetAllPrimeWeight p n a)
      (targetNormalizedWeight (K:=ℚ) n) := by
  let B := Nat.log p (800*n)
  have hw (b : ℕ) (hb : b≤100*n) (t : ℤ) (ht : t∈poleWindow b) :
      truncatedRootValuation p B (a-t)≤B := by
    apply truncatedRootValuation_le_log (800*n) B (a-t) ?_ le_rfl
    apply (root_difference_le (100*n) a t ha ?_).trans (by omega)
    simp only [poleWindow,Finset.mem_Icc] at ht ⊢
    omega
  have hN : ScaledLaurentPadicLower p (a:ℚ) B (targetNormalizationValuation p n)
      (RatFunc.C (targetNormalization (K:=ℚ) n)) :=
    ScaledLaurentPadicLower.constant (Or.inr (by rw [targetNormalization_padicVal]))
  have h2 := ScaledLaurentPadicLower.constant (a:=(a:ℚ)) (s:=(B:ℤ)) (PadicLower.natCast (p:=p) 2)
  have hx := scaledLinearFactor_laurent (p:=p) B a 0 1
    (by simpa using hw 0 (by omega) 0 (by simp [poleWindow]))
  simp only [one_mul,sub_zero,Int.cast_one,Int.cast_zero,map_one,map_zero] at hx
  have hD := (centeredDenominator_scaledLaurent (p:=p) B a 1 (100*n)
    (by simpa using hw (100*n) le_rfl)).pow 5
  simp only [one_mul,Int.cast_one,map_one,comp_X] at hD
  have hQ := ScaledLaurentPadicLower.prod (p:=p) Finset.univ (a:ℚ) B
    (fun i : Fin 15 => -truncatedCenteredCount p B a (targetEndpointTuple n i))
    (fun i => (algebraMap ℚ[X] (RatFunc ℚ) (centeredDenominator (targetEndpointTuple n i)))⁻¹)
    (fun i hi => inverseCenteredDenominator_scaledLaurent B a _
      (hw _ ((targetEndpointTuple_le_67 n i).trans (by omega))))
  have h := hN.mul (((h2.mul hx).mul hD).mul hQ)
  convert h using 1 <;> try rfl
  · simp [targetAllPrimeWeight,Finset.sum_neg_distrib,B]
    ring
  · simp [targetNormalizedWeight,tupleWeight,tupleNumerator,tupleDenominator,
      div_eq_mul_inv,Finset.prod_inv_distrib,mul_assoc]
end OddZeta.FourValue

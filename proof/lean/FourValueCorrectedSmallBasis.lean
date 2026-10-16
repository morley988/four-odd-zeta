import FourValueCorrectedSelected

/-! Prime-power root counting for E_i(x²), including the prime 2.
The physical-coordinate checkpoint remains unchanged; this namespace supplies
the arithmetic statements for the analytic-coordinate matrix. -/

noncomputable section
namespace OddZeta.FourValue.Corrected
open Polynomial
open scoped RatFunc
variable {p : ℕ} [Fact p.Prime]
theorem squareBasis_analytic_factorization (j : ℕ) :
    (squareBasisPolynomial (K:=ℚ) (j+1)).comp (X^2) =
      C (2/((2*(j+1)).factorial:ℚ))*X*centeredDenominator j := by
  simp only [squareBasisPolynomial,Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,
    mul_comp,C_comp,squareRootProduct_square_comp]
  ring

theorem target_basis_root_difference (n j : ℕ) (hj : j≤targetHankelDegree n)
    (a t : ℤ) (ha : a∈poleWindow (100*n)) (ht : t∈poleWindow j) :
    (a-t).natAbs≤800*n := by
  simp only [poleWindow,Finset.mem_Icc] at ha ht
  unfold targetHankelDegree at hj
  have h : |a-t|≤(800*n:ℕ) := by rw [abs_le]; push_cast; constructor <;> omega
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

theorem truncatedCenteredCount_factorial_lower (n j : ℕ) (hj : j+1≤targetHankelDegree n)
    (a : ℤ) (ha : a∈poleWindow (100*n)) :
    -(padicValNat p (2*(j+1)).factorial:ℤ)+
      truncatedCenteredCount p (Nat.log p (800*n)) (a) j ≥ -3*(Nat.log p (800*n):ℤ) := by
  have hj' : 2*(j+1)≤800*n := by unfold targetHankelDegree at hj; omega
  rw [truncatedCenteredCount_sum _ (800*n) _ _
    (fun t ht => target_basis_root_difference n j (by omega) a t ha ht) le_rfl,
    padicValNat_factorial (b:=Nat.log p (800*n)+1)
      (by have h := Nat.log_mono_right (b:=p) hj'; omega)]
  push_cast
  have hs := Finset.sum_le_sum (s:=Finset.Ico 1 (Nat.log p (800*n)+1))
    (fun e he => centeredCount_factorial_loss (p^e) j (pow_pos (Fact.out : p.Prime).pos _) (a))
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Nat.card_Ico,Nat.add_sub_cancel,nsmul_eq_mul] at hs
  push_cast at hs
  linarith

theorem squareBasis_analytic_scaledLaurent (n : ℕ) (i : Fin (targetHankelDegree n+1))
    (a : ℤ) (ha : a∈poleWindow (100*n)) :
    ScaledLaurentPadicLower p (a:ℚ) (Nat.log p (800*n)) (-3*(Nat.log p (800*n):ℤ))
      (algebraMap ℚ[X] (RatFunc ℚ)
        ((squareBasisPolynomial i.val).comp (X^2))) := by
  cases hi : i.val with
  | zero =>
    simp only [squareBasisPolynomial,hi,ite_true,one_comp,map_one]
    exact (ScaledLaurentPadicLower.one (p:=p) (a:ℚ) (Nat.log p (800*n))).mono (by omega)
  | succ j =>
    rw [squareBasis_analytic_factorization,map_mul,map_mul]
    have hj : j+1≤targetHankelDegree n := by have h := i.isLt; omega
    have hw (t : ℤ) (ht : t∈poleWindow j) :
        truncatedRootValuation p (Nat.log p (800*n)) (a-t)≤Nat.log p (800*n) :=
      truncatedRootValuation_le_log (800*n) _ _
        (target_basis_root_difference n j (by omega) a t ha ht) le_rfl
    have hx := scaledLinearFactor_laurent (p:=p) (Nat.log p (800*n)) a 0 1
      (by simpa using hw 0 (by simp [poleWindow]))
    simp only [Int.cast_ofNat,Int.cast_zero,map_zero,sub_zero,one_mul] at hx
    have hD := centeredDenominator_scaledLaurent (p:=p) (Nat.log p (800*n)) a 1 j (by simpa using hw)
    simp only [Int.cast_one,map_one,one_mul,comp_X] at hx hD
    have hfac : PadicLower p (-(padicValNat p (2*(j+1)).factorial:ℤ))
        (2/((2*(j+1)).factorial:ℚ)) := by
      have h : PadicLower p (-(padicValNat p (2*(j+1)).factorial:ℤ))
          (((2*(j+1)).factorial:ℚ)⁻¹) := Or.inr (by simp)
      simpa [div_eq_mul_inv] using (PadicLower.natCast (p:=p) 2).mul h
    have h := ((ScaledLaurentPadicLower.constant (a:=(a:ℚ)) (s:=(Nat.log p (800*n):ℤ)) hfac).mul hx).mul hD
    have h' := h.mono (v:=-3*(Nat.log p (800*n):ℤ)) (by
      have hroot : 0≤truncatedRootValuation p (Nat.log p (800*n)) (a) := by
        unfold truncatedRootValuation
        split_ifs <;> omega
      have hb := truncatedCenteredCount_factorial_lower (p:=p) n j hj a ha
      omega)
    simpa using h' 


end OddZeta.FourValue.Corrected

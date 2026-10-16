import FourValueAllPrimeWeight
import FourValueSquareBasisFactorization

noncomputable section
namespace OddZeta.FourValue
open Polynomial
open scoped RatFunc
variable {p : ℕ} [Fact p.Prime]

theorem ScaledLaurentPadicLower.mono {a : ℚ} {s w v : ℤ} {f : RatFunc ℚ}
    (hf : ScaledLaurentPadicLower p a s w f) (hvw : v≤w) :
    ScaledLaurentPadicLower p a s v f := by
  intro j
  exact (hf j).mono (by omega)

theorem centeredCount_factorial_loss (q j : ℕ) (hq : 0<q) (a : ℤ) :
    ((2*(j+1)/q:ℕ):ℤ)-3≤centeredResidueCount q a j := by
  have hp : 0<(q:ℤ) := by exact_mod_cast hq
  have hc := (centeredResidueCount_scaled_bounds q hq a j).1
  have hd : (q:ℤ)*((2*(j+1)/q:ℕ):ℤ)≤2*((j:ℤ)+1) := by
    exact_mod_cast Nat.mul_div_le (2*(j+1)) q
  nlinarith

theorem target_basis_root_difference (n j : ℕ) (hj : j≤targetHankelDegree n)
    (a t : ℤ) (ha : a∈poleWindow (100*n)) (ht : t∈poleWindow j) :
    (2*a-t).natAbs≤800*n := by
  simp only [poleWindow,Finset.mem_Icc] at ha ht
  unfold targetHankelDegree at hj
  have h : |2*a-t|≤(800*n:ℕ) := by rw [abs_le]; push_cast; constructor <;> omega
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

theorem truncatedCenteredCount_factorial_lower (n j : ℕ) (hj : j+1≤targetHankelDegree n)
    (a : ℤ) (ha : a∈poleWindow (100*n)) :
    -(padicValNat p (2*(j+1)).factorial:ℤ)+
      truncatedCenteredCount p (Nat.log p (800*n)) (2*a) j ≥ -3*(Nat.log p (800*n):ℤ) := by
  have hj' : 2*(j+1)≤800*n := by unfold targetHankelDegree at hj; omega
  rw [truncatedCenteredCount_sum _ (800*n) _ _
    (fun t ht => target_basis_root_difference n j (by omega) a t ha ht) le_rfl,
    padicValNat_factorial (b:=Nat.log p (800*n)+1)
      (by have h := Nat.log_mono_right (b:=p) hj'; omega)]
  push_cast
  have hs := Finset.sum_le_sum (s:=Finset.Ico 1 (Nat.log p (800*n)+1))
    (fun e he => centeredCount_factorial_loss (p^e) j (pow_pos (Fact.out : p.Prime).pos _) (2*a))
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Nat.card_Ico,Nat.add_sub_cancel,nsmul_eq_mul] at hs
  push_cast at hs
  linarith

theorem squareBasis_physical_scaledLaurent (n : ℕ) (i : Fin (targetHankelDegree n+1))
    (a : ℤ) (ha : a∈poleWindow (100*n)) :
    ScaledLaurentPadicLower p (a:ℚ) (Nat.log p (800*n)) (-3*(Nat.log p (800*n):ℤ))
      (algebraMap ℚ[X] (RatFunc ℚ)
        (((squareBasisPolynomial i.val).comp (C 4*X)).comp (X^2))) := by
  cases hi : i.val with
  | zero =>
    simp only [squareBasisPolynomial,hi,ite_true,one_comp,map_one]
    exact (ScaledLaurentPadicLower.one (p:=p) (a:ℚ) (Nat.log p (800*n))).mono (by omega)
  | succ j =>
    rw [squareBasis_physical_factorization,map_mul,map_mul]
    have hj : j+1≤targetHankelDegree n := by have h := i.isLt; omega
    have hw (t : ℤ) (ht : t∈poleWindow j) :
        truncatedRootValuation p (Nat.log p (800*n)) (2*a-t)≤Nat.log p (800*n) :=
      truncatedRootValuation_le_log (800*n) _ _
        (target_basis_root_difference n j (by omega) a t ha ht) le_rfl
    have hx := scaledLinearFactor_laurent (p:=p) (Nat.log p (800*n)) a 0 2
      (hw 0 (by simp [poleWindow]))
    simp only [Int.cast_ofNat,Int.cast_zero,map_zero,sub_zero] at hx
    have hD := centeredDenominator_scaledLaurent (p:=p) (Nat.log p (800*n)) a 2 j hw
    have hfac : PadicLower p (-(padicValNat p (2*(j+1)).factorial:ℤ))
        (2/((2*(j+1)).factorial:ℚ)) := by
      have h : PadicLower p (-(padicValNat p (2*(j+1)).factorial:ℤ))
          (((2*(j+1)).factorial:ℚ)⁻¹) := Or.inr (by simp)
      simpa [div_eq_mul_inv] using (PadicLower.natCast (p:=p) 2).mul h
    have h := ((ScaledLaurentPadicLower.constant (a:=(a:ℚ)) (s:=(Nat.log p (800*n):ℤ)) hfac).mul hx).mul hD
    apply h.mono
    have hroot : 0≤truncatedRootValuation p (Nat.log p (800*n)) (2*a) := by
      unfold truncatedRootValuation
      split_ifs <;> omega
    have hb := truncatedCenteredCount_factorial_lower (p:=p) n j hj a ha
    omega
end OddZeta.FourValue

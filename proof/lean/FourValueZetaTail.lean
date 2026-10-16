import FourValueCoefficientDifference
import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section
namespace OddZeta.FourValue
open Polynomial

theorem hasSum_zeta_nat (s : ℕ) (hs : 1<s) :
    HasSum (fun r : ℕ => 1/(r:ℂ)^s) (riemannZeta (s:ℂ)) := by
  have h : Summable (fun r : ℕ => 1/(r:ℂ)^s) := by
    simpa only [Complex.cpow_natCast] using
      (Complex.summable_one_div_nat_cpow (p:=(s:ℂ))).mpr (by exact_mod_cast hs)
  rw [zeta_nat_eq_tsum_of_gt_one hs]
  exact h.hasSum

theorem hasSum_zeta_positive (s : ℕ) (hs : 1<s) :
    HasSum (fun r : ℕ => 1/((r+1:ℕ):ℂ)^s) (riemannZeta (s:ℂ)) := by
  have h := (hasSum_nat_add_iff' (f:=fun r : ℕ => 1/(r:ℂ)^s) 1).mpr
    (hasSum_zeta_nat s hs)
  simpa [ne_of_gt (lt_trans Nat.zero_lt_one hs)] using h

theorem hasSum_zeta_tail (m s : ℕ) (hs : 1<s) :
    HasSum (fun r : ℕ => 1/((r+m+1:ℕ):ℂ)^s)
      (riemannZeta (s:ℂ)-finiteHarmonic (K:=ℂ) m s) := by
  exact (hasSum_nat_add_iff' (f:=fun r : ℕ => 1/((r+1:ℕ):ℂ)^s) m).mpr
    (hasSum_zeta_positive s hs)

theorem hasSum_integer_pole_tail (b h : ℕ) (hh : 1≤h) (j : ℤ)
    (hj : j∈poleWindow b) (k : ℕ) :
    HasSum (fun r : ℕ => rationalCoefficientAt ((r+b+1:ℕ):ℂ) h
      (rationalPole (j:ℂ) (k+1)))
      ((-1:ℂ)^h*(Nat.choose (k+h) h:ℂ)*
        (riemannZeta ((k+h+1:ℕ):ℂ)-finiteHarmonic ((b-j).toNat) (k+h+1))) := by
  have hjb : j≤(b:ℤ) := (Finset.mem_Icc.mp hj).2
  have ht (r : ℕ) : ((r+b+1:ℕ):ℂ)≠(j:ℂ) := by
    have hi : ((r+b+1:ℕ):ℤ)≠j := by omega
    exact_mod_cast hi
  have hcast (r : ℕ) : ((r+b+1:ℕ):ℂ)-(j:ℂ)=((r+(b-j).toNat+1:ℕ):ℂ) := by
    have hi : ((r+b+1:ℕ):ℤ)-j=((r+(b-j).toNat+1:ℕ):ℤ) := by omega
    exact_mod_cast hi
  have H := (hasSum_zeta_tail (b-j).toNat (k+h+1) (by omega)).mul_left
    ((-1:ℂ)^h*(Nat.choose (k+h) h:ℂ))
  apply H.congr_fun
  intro r
  rw [rationalCoefficientAt_pole_regular _ _ (ht r),hcast]
  ring

/-- A genuinely convergent series identity for every finite partial fraction
expansion, with the exact Laurent/Taylor normalization retained. -/
theorem hasSum_partialFraction_taylor (b h : ℕ) (hh : 1≤h)
    (f : RatFunc ℂ) (c : ℤ → Fin 10 → ℂ)
    (hf : f=∑ j ∈ poleWindow b, ∑ k : Fin 10, c j k • rationalPole (j:ℂ) (k.val+1)) :
    HasSum (fun r : ℕ => rationalCoefficientAt ((r+b+1:ℕ):ℂ) h f)
      (∑ j ∈ poleWindow b, ∑ k : Fin 10, c j k *
        ((-1:ℂ)^h*(Nat.choose (k.val+h) h:ℂ)*
          (riemannZeta ((k.val+h+1:ℕ):ℂ)-finiteHarmonic ((b-j).toNat) (k.val+h+1)))) := by
  have H := hasSum_sum (s:=poleWindow b) (fun j hj =>
    hasSum_sum (s:=Finset.univ) (fun k _ =>
      (hasSum_integer_pole_tail b h hh j hj k.val).mul_left (c j k)))
  apply H.congr_fun
  intro r
  simp [hf,smul_eq_mul]

end OddZeta.FourValue

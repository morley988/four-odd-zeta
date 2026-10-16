import FourValueScaledBasisBounds
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Data.Nat.Choose.Bounds

noncomputable section
namespace OddZeta.FourValue
open Polynomial

theorem complex_multiset_prod_bound (s : Multiset ℂ) (R : ℝ) (hR : 0≤R)
    (hs : ∀ z∈s,‖z‖≤R) : ‖s.prod‖≤R^s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    rw [Multiset.prod_cons,norm_mul,Multiset.card_cons,pow_succ]
    have ha := hs a (by simp)
    have ht := ih (fun z hz => hs z (by simp [hz]))
    simpa [mul_comm] using mul_le_mul ha ht (norm_nonneg _) hR

theorem complex_esymm_bound (s : Multiset ℂ) (R : ℝ) (hR : 0≤R)
    (hs : ∀ z∈s,‖z‖≤R) (k : ℕ) : ‖s.esymm k‖≤(s.card.choose k:ℝ)*R^k := by
  unfold Multiset.esymm
  apply (norm_multiset_sum_le _).trans
  have h := Multiset.sum_le_card_nsmul
    ((s.powersetCard k).map Multiset.prod |>.map (fun z : ℂ => ‖z‖)) (R^k) (by
      intro x hx
      obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨t,ht,rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨hts,htcard⟩ := Multiset.mem_powersetCard.mp ht
      rw [← htcard]
      exact complex_multiset_prod_bound t R hR (fun z hz => hs z (Multiset.mem_of_le hts hz)))
  simpa [Multiset.card_map,Multiset.card_powersetCard,nsmul_eq_mul] using h

theorem monic_root_coefficient_bound (P : ℂ[X]) (hP : P.Monic) (R : ℝ) (hR : 0≤R)
    (hroot : ∀ z : ℂ,P.eval z=0 → ‖z‖≤R) (j : ℕ) (hj : j≤P.natDegree) :
    ‖P.coeff j‖≤(P.natDegree.choose (P.natDegree-j):ℝ)*R^(P.natDegree-j) := by
  have hcard := splits_iff_card_roots.mp (IsAlgClosed.splits P)
  rw [coeff_eq_esymm_roots_of_card hcard hj,hP.leadingCoeff,one_mul,norm_mul,norm_pow,
    norm_neg,norm_one,one_pow,one_mul]
  have h := complex_esymm_bound P.roots R hR
    (fun z hz => hroot z ((mem_roots hP.ne_zero).mp hz)) (P.natDegree-j)
  rwa [hcard] at h

theorem monic_root_coefficient_power_bound (P : ℂ[X]) (hP : P.Monic) (R : ℝ) (hR : 0≤R)
    (hroot : ∀ z : ℂ,P.eval z=0 → ‖z‖≤R) (m j : ℕ) (hm : P.natDegree≤m)
    (hj : j≤P.natDegree) : ‖P.coeff j‖≤((m:ℝ)*R)^(P.natDegree-j) := by
  have hc : (P.natDegree.choose (P.natDegree-j):ℝ)≤(m:ℝ)^(P.natDegree-j) := by
    exact_mod_cast (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hm _)
  apply (monic_root_coefficient_bound P hP R hR hroot j hj).trans
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hc (pow_nonneg hR _)

theorem concreteAnalyticBasis_coefficient_bound (i m : ℕ) (hi : i≤m) (w : Fin 45→ℝ)
    (hw : ∀ l,0≤w l) (hs : ∑ l,w l=1) (j : ℕ) (hj : j ≤ i) :
    ‖(concreteAnalyticBasis i w).coeff j‖≤(3*(m:ℝ))^(i-j) := by
  have hd := concreteAnalyticBasis_natDegree i w hw hs
  have h := monic_root_coefficient_power_bound (concreteAnalyticBasis i w)
    (concreteAnalyticBasis_monic i w) 3 (by norm_num)
    (fun z hz => (concreteAnalyticBasis_root_bound i w z hz).trans (by norm_num))
    m j (by omega) (by omega)
  simpa [hd,mul_comm] using h
end OddZeta.FourValue

import FourValueGlobalLocal

noncomputable section
namespace OddZeta.FourValue.Corrected
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]

/-- Cancelled poles outside the actual support contribute zero. -/
theorem observation_zero_outside (n b : ℕ) (a : ℤ) (lambda : Fin 4 → ℚ) (P : ℚ[X])
 (ha : a∉poleWindow (63*n)) :
 localFourValueObservation b a lambda (rationalAnalyticTest n P)=0 := by
 have hn : a∉targetPoleList n := fun h => ha (targetPoleList_bound n a h)
 have hc : (targetPoleList n).count a=0 := List.count_eq_zero.mpr hn
 have hz (j : ℤ) (hj : j<0) : rationalCoefficientAt (a:ℚ) j (rationalAnalyticTest n P)=0 := by
   simpa using rationalAnalyticTest_divisible_regular n a P 1 (by simp [hc]) j hj
 unfold localFourValueObservation localFourthObservation
 simp only [hz (-3) (by omega),hz (-5) (by omega),hz (-7) (by omega),hz (-9) (by omega),mul_zero,add_zero]
 rw [Finset.sum_eq_zero]
 · simp
 · intro k hk
   simp only [hz (-((k+1:ℕ):ℤ)) (by omega),mul_zero]

theorem rationalFourValueFunctional_local_sum_63 (n : ℕ) (lambda : Fin 4 → ℚ) (P : ℚ[X])
 (hP : P.natDegree≤361*n+3) :
 rationalFourValueFunctional n lambda P =
 ∑ a ∈ poleWindow (63*n),localFourValueObservation (67*n) a lambda (rationalAnalyticTest n P) := by
 rw [rationalFourValueFunctional_local_sum_67 n lambda P hP]
 symm
 apply Finset.sum_subset
 · intro a ha
   simp only [poleWindow,mem_Icc] at ha ⊢
   omega
 · intro a ha hn
   exact observation_zero_outside n (67*n) a lambda P hn

def residueRemainder (p : ℕ) (a : ℤ) : ℕ := (a%(p:ℤ)).toNat

theorem residueRemainder_lt (a : ℤ) : residueRemainder p a<p := by
 have hp : 0<(p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
 have h0 := Int.emod_nonneg a hp.ne'
 have h1 := Int.emod_lt_of_pos a hp
 unfold residueRemainder
 omega

/-- Each pair of residues ±r is represented exactly once, including r=0. -/
def pairedLabel (a : ℤ) : Fin (p/2+1) :=
 ⟨min (residueRemainder p a) (p-residueRemainder p a),by
   have := residueRemainder_lt (p:=p) a
   omega⟩

theorem pairedLabel_congruence (a : ℤ) :
 (p:ℤ)∣a-(pairedLabel (p:=p) a).val ∨ (p:ℤ)∣a+(pairedLabel (p:=p) a).val := by
 have hp : 0<(p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
 have h0 := Int.emod_nonneg a hp.ne'
 have h1 := residueRemainder_lt (p:=p) a
 have hcast : (residueRemainder p a:ℤ)=a%(p:ℤ) := by simp [residueRemainder,Int.toNat_of_nonneg h0]
 have he := Int.mul_ediv_add_emod a (p:ℤ)
 by_cases hl : residueRemainder p a≤p-residueRemainder p a
 · left
   simp only [pairedLabel,min_eq_left hl]
   refine ⟨a/(p:ℤ),?_⟩
   rw [hcast]
   omega
 · right
   simp only [pairedLabel,min_eq_right (by omega : p-residueRemainder p a≤residueRemainder p a)]
   refine ⟨a/(p:ℤ)+1,?_⟩
   rw [Nat.cast_sub (by omega : residueRemainder p a≤p),hcast]
   nlinarith

def pairedPoles (n : ℕ) (r : Fin (p/2+1)) : Finset ℤ :=
 (poleWindow (63*n)).filter (fun a => pairedLabel (p:=p) a=r)

theorem mem_pairedPoles (n : ℕ) (r : Fin (p/2+1)) (a : ℤ) (ha : a∈pairedPoles n r) :
 a∈poleWindow (63*n) ∧ ((p:ℤ)∣a-r.val ∨ (p:ℤ)∣a+r.val) := by
 obtain ⟨haw,har⟩ := mem_filter.mp ha
 refine ⟨haw,?_⟩
 simpa only [har] using pairedLabel_congruence (p:=p) a

theorem rationalFourValueMatrix_paired_partition (n : ℕ) (lambda : Fin 4 → ℚ) {k : ℕ}
 (rows cols : Fin k → Fin (targetHankelDegree n+1)) :
 (rationalFourValueMatrix n lambda).submatrix rows cols =
 ∑ r : Fin (p/2+1),selectedResidueMatrix n (67*n) (pairedPoles n r) lambda rows cols := by
 ext i j
 change rationalFourValueFunctional n lambda
   (squareBasisPolynomial (rows i).val*squareBasisPolynomial (cols j).val)=_
 rw [rationalFourValueFunctional_local_sum_63]
 · simp only [Matrix.sum_apply,selectedResidueMatrix,polynomialGram,residuePolynomialFunctional_apply,pairedPoles]
   exact (sum_fiberwise (poleWindow (63*n)) (pairedLabel (p:=p)) _).symm
 · have h := Polynomial.natDegree_mul_le (p:=squareBasisPolynomial (K:=ℚ) (rows i).val)
     (q:=squareBasisPolynomial (cols j).val)
   rw [squareBasisPolynomial_degree,squareBasisPolynomial_degree] at h
   have hr := (rows i).isLt
   have hc := (cols j).isLt
   unfold targetHankelDegree at hr hc
   omega

end OddZeta.FourValue.Corrected

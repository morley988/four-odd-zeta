import FourValueFiniteGrid

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem tupleEvenWeight_padded (b : ℕ) (a : Fin 15 → ℕ) (ha : ∀ i,a i≤b) :
    tupleEvenWeight (K:=K) b a =
      algebraMap K[X] (RatFunc K) (C 2*tupleWeightPadding b a) /
      algebraMap K[X] (RatFunc K) ((centeredDenominator b)^10) := by
  have hD : algebraMap K[X] (RatFunc K) (tupleDenominator (K:=K) a)≠0 :=
    RatFunc.algebraMap_ne_zero (tupleDenominator_monic a).ne_zero
  have hR : algebraMap K[X] (RatFunc K) (centeredDenominator (K:=K) b)≠0 :=
    RatFunc.algebraMap_ne_zero (centeredDenominator_monic b).ne_zero
  have hpad := congrArg (algebraMap K[X] (RatFunc K))
    (tupleWeightPadding_product (K:=K) b a ha)
  simp only [map_mul,map_pow] at hpad
  unfold tupleEvenWeight
  simp only [map_mul,map_pow,map_ofNat]
  field_simp
  linear_combination -hpad

theorem rationalCoefficientAt_polynomial_dvd (t : K) (p : K[X]) (r : ℕ)
    (hp : (X-C t)^r ∣ p) (h : ℤ) (hh : h<r) :
    rationalCoefficientAt t h (algebraMap K[X] (RatFunc K) p)=0 := by
  by_cases hn : h<0
  · exact rationalCoefficientAt_polynomial_neg t p h hn
  · lift h to ℕ using (by omega : 0≤h)
    obtain ⟨v,rfl⟩ := hp
    simpa using rationalCoefficientAt_boundary_factor t v 1 (by simp) r h (by omega)

def gridAnnihilator (b : ℕ) : K[X] :=
  ((centeredDenominator b).comp (C ((2:K)⁻¹)*X))^15

theorem gridAnnihilator_scaled (b : ℕ) :
    (gridAnnihilator (K:=K) b).comp (C 2*X)=(centeredDenominator b)^15 := by
  simp only [gridAnnihilator,Polynomial.pow_comp,Polynomial.comp_assoc,
    Polynomial.mul_comp,Polynomial.C_comp,Polynomial.X_comp]
  have heq : C ((2:K)⁻¹)*(C 2*X)=(X:K[X]) := by
    rw [← mul_assoc,← map_mul,inv_mul_cancel₀ (by norm_num),map_one,one_mul]
  rw [heq,Polynomial.comp_X]

theorem gridAnnihilator_ne_zero (b : ℕ) : gridAnnihilator (K:=K) b≠0 := by
  intro hz
  have heq := gridAnnihilator_scaled (K:=K) b
  rw [hz,Polynomial.zero_comp] at heq
  exact pow_ne_zero 15 (centeredDenominator_monic b).ne_zero heq.symm

theorem rawGridFunctional_annihilates (b : ℕ) (a : Fin 15 → ℕ)
    (ha : ∀ i,a i≤b) (h : ℤ) (hh : h<5) (f : K[X]) :
    rawGridFunctional b a h (gridAnnihilator b*f)=0 := by
  have heq : tupleEvenWeight b a * algebraMap K[X] (RatFunc K)
      ((gridAnnihilator b*f).comp (C 2*X)) =
      algebraMap K[X] (RatFunc K)
        ((centeredDenominator b)^5*(C 2*tupleWeightPadding b a*f.comp (C 2*X))) := by
    rw [tupleEvenWeight_padded b a ha,Polynomial.mul_comp,gridAnnihilator_scaled]
    simp only [map_mul,map_pow]
    have hn := RatFunc.algebraMap_ne_zero (K:=K) (centeredDenominator_monic (K:=K) b).ne_zero
    field_simp
  change rationalGrid b h _=0
  rw [heq]
  simp only [rationalGrid,LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  apply rationalCoefficientAt_polynomial_dvd (j:K) _ 5 _ h hh
  apply dvd_mul_of_dvd_left
  apply pow_dvd_pow_of_dvd
  apply Polynomial.dvd_iff_isRoot.mpr
  apply (centeredDenominator_eval_zero_iff b (j:K)).mpr
  exact ⟨j,(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2,rfl⟩

theorem finiteGridFunctional_finite (b : ℕ) (a : Fin 15 → ℕ)
    (ha : ∀ i,a i≤b) (h : ℤ) (hh : h<5) :
    ∃ p : K[X], p≠0 ∧ ∀ f : K[X], finiteGridFunctional b a h (p*f)=0 := by
  let p : K[X] := gridAnnihilator b
  have hp : p≠0 := gridAnnihilator_ne_zero b
  have hr : p.comp (-X)≠0 := by
    intro hz
    have heq := congrArg (fun q : K[X] => q.comp (-X)) hz
    rw [Polynomial.comp_neg_X_comp_neg_X,Polynomial.zero_comp] at heq
    exact hp heq
  refine ⟨p*p.comp (-X),mul_ne_zero hp hr,?_⟩
  intro f
  have h₁ : rawGridFunctional b a h ((p*p.comp (-X))*f)=0 := by
    rw [mul_assoc]
    exact rawGridFunctional_annihilates b a ha h hh _
  have h₂ : rawGridFunctional b a h (((p*p.comp (-X))*f).comp (-X))=0 := by
    simp only [Polynomial.mul_comp,Polynomial.comp_neg_X_comp_neg_X]
    rw [mul_comm (p.comp (-X)) p,mul_assoc]
    exact rawGridFunctional_annihilates b a ha h hh _
  change (2:K)⁻¹ * (_-_) = 0
  rw [h₁,h₂,sub_self,mul_zero]

/-- An actual finite odd Pearson solution for every integer Laurent order below five. -/
theorem finiteGridFunctional_isFinitePearson (b : ℕ) (a : Fin 15 → ℕ)
    (ha : ∀ i,a i≤b) (h : ℤ) (hh : h<5) :
    IsFinitePearson (tuplePearsonPolynomial b a) (finiteGridFunctional (K:=K) b a h) :=
  ⟨finiteGridFunctional_finite b a ha h hh,
    finiteGridFunctional_odd b a h,finiteGridFunctional_pearson b a ha h hh⟩

end OddZeta.FourValue

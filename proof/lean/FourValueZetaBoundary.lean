import FourValueNormalization
import FourValueBoundaryZero
import FourValueZetaIdentity

noncomputable section
namespace OddZeta.FourValue
open Polynomial

theorem centeredDenominator_complex_ne_zero_above (a t : ℕ) (ht : a<t) :
    (centeredDenominator (K:=ℂ) a).eval (t:ℂ)≠0 := by
  intro hz
  obtain ⟨j,_,hj,heq⟩ := (centeredDenominator_eval_zero_iff a (t:ℂ)).mp hz
  have heq' : (t:ℤ)=j := by exact_mod_cast heq
  omega

theorem tupleRationalTest_fraction (b : ℕ) (a : Fin 15 → ℕ) (p : ℂ[X]) :
    tupleRationalTest b a p =
      algebraMap ℂ[X] (RatFunc ℂ) (tupleNumerator b*p.comp (X^2)) /
        algebraMap ℂ[X] (RatFunc ℂ) (tupleDenominator a) := by
  change (algebraMap ℂ[X] (RatFunc ℂ) (tupleNumerator b) /
    algebraMap ℂ[X] (RatFunc ℂ) (tupleDenominator a))*
    algebraMap ℂ[X] (RatFunc ℂ) (p.comp (X^2)) = _
  rw [map_mul]
  ring

theorem tupleRationalTest_zero_at_gap (b t : ℕ) (a : Fin 15 → ℕ)
    (hta : ∀ i,a i<t) (htb : t≤b) (p : ℂ[X]) (h : ℕ) (hh : h<5) :
    rationalCoefficientAt (t:ℂ) h (tupleRationalTest b a p)=0 := by
  have hD : (tupleDenominator (K:=ℂ) a).eval (t:ℂ)≠0 := by
    simp only [tupleDenominator,Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => centeredDenominator_complex_ne_zero_above _ _ (hta i))
  have hr : (centeredDenominator (K:=ℂ) b).eval (t:ℂ)=0 :=
    (centeredDenominator_eval_zero_iff b (t:ℂ)).mpr ⟨t,by omega,by omega,by simp⟩
  obtain ⟨v,hv⟩ := (Polynomial.dvd_iff_isRoot).mpr hr
  have hnum : tupleNumerator b*p.comp (X^2) =
      (X-C (t:ℂ))^5*(C 2*X*v^5*p.comp (X^2)) := by
    rw [tupleNumerator,hv]; ring
  rw [tupleRationalTest_fraction,hnum]
  exact rationalCoefficientAt_boundary_factor _ _ _ hD 5 h hh

theorem targetEndpointTuple_le_67 (n : ℕ) (i : Fin 15) : targetEndpointTuple n i≤67*n := by
  fin_cases i <;> simp [targetEndpointTuple] <;> omega

/-- The actual normalized rational test; the input polynomial uses physical X. -/
def targetZetaTest (n : ℕ) (p : ℂ[X]) : RatFunc ℂ :=
  targetNormalization (K:=ℂ) n • tupleRationalTest (100*n) (targetEndpointTuple n) (p.comp (C 4*X))

theorem targetZetaTest_gap_zero (n t : ℕ) (ht : 67*n<t) (ht' : t≤100*n)
    (p : ℂ[X]) (h : ℕ) (hh : h<5) :
    rationalCoefficientAt (t:ℂ) h (targetZetaTest n p)=0 := by
  rw [targetZetaTest,map_smul,tupleRationalTest_zero_at_gap (100*n) t _
    (fun i => lt_of_le_of_lt (targetEndpointTuple_le_67 n i) ht) ht' _ h hh,smul_zero]

theorem targetZetaTest_partialFractions (n : ℕ) (p : ℂ[X]) (hp : p.natDegree≤361*n+3) :
    ∃ c : ℤ → Fin 10 → ℂ, targetZetaTest n p =
      ∑ j ∈ poleWindow (100*n),∑ k : Fin 10,c j k • rationalPole (j:ℂ) (k.val+1) := by
  have hdeg : ((p.comp (C 4*X)).natDegree:ℤ)≤tupleBeta (100*n) (targetEndpointTuple n)+3 := by
    rw [targetEndpointTuple_beta]
    have hd := Polynomial.natDegree_comp_le (p:=p) (q:=(C 4*X:ℂ[X]))
    have h4 : (C 4*X:ℂ[X]).natDegree=1 := by
      rw [Polynomial.natDegree_C_mul (by norm_num : (4:ℂ)≠0),Polynomial.natDegree_X]
    rw [h4,mul_one] at hd
    omega
  obtain ⟨c,hc⟩ := tupleRationalTest_partialFractions (100*n) (targetEndpointTuple n)
    (targetEndpointTuple_bounded n) (p.comp (C 4*X)) hdeg
  refine ⟨fun j k => targetNormalization n*c j k,?_⟩
  simp [targetZetaTest,hc,Finset.smul_sum,smul_smul]

theorem targetZetaTest_reflect (n : ℕ) (p : ℂ[X]) :
    rationalReflect (targetZetaTest n p) = -targetZetaTest n p := by
  rw [targetZetaTest,rationalReflect_complex_smul,tupleRationalTest_reflect,smul_neg]

theorem targetZetaTest_B1 (n : ℕ) (p : ℂ[X]) (hp : p.natDegree≤361*n+3) :
    rationalB (100*n) 1 (targetZetaTest n p)=0 := by
  rw [targetZetaTest,map_smul]
  have hd : ((p.comp (C 4*X)).natDegree:ℤ)≤tupleBeta (100*n) (targetEndpointTuple n)+3 := by
    rw [targetEndpointTuple_beta]
    have h := Polynomial.natDegree_comp_le (p:=p) (q:=(C 4*X:ℂ[X]))
    have h4 : (C 4*X:ℂ[X]).natDegree=1 := by
      rw [Polynomial.natDegree_C_mul (by norm_num : (4:ℂ)≠0),Polynomial.natDegree_X]
    rw [h4,mul_one] at h
    omega
  change targetNormalization n • concreteB (100*n) (targetEndpointTuple n) 1 (p.comp (C 4*X))=0
  rw [concreteB_one_zero _ _ (targetEndpointTuple_bounded n) _ hd,smul_zero]

end OddZeta.FourValue

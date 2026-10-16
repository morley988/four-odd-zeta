import FourValueProperFractions
import FourValueBoundaryZero
import FourValueRationalFamily

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def tuplePadding (b : ℕ) (a : Fin 15 → ℕ) : K[X] := ∏ i, endpointPadding b (a i)

def pearsonBoundaryNumerator (b : ℕ) (a : Fin 15 → ℕ) (q : K[X]) : K[X] :=
  C (2^21:K)*(X-C (b:K))^5*(X+C ((b+1:ℕ):K))^5 *
    q.comp ((C 2*X+1)^2) * tuplePadding b a

def pearsonBoundaryFunction (b : ℕ) (a : Fin 15 → ℕ) (q : K[X]) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (pearsonBoundaryNumerator b a q) /
    algebraMap K[X] (RatFunc K) ((endpointDenominator b)^10)

theorem tuplePadding_ne_zero (b : ℕ) (a : Fin 15 → ℕ) (ha : ∀ i,a i≤b) :
    tuplePadding (K:=K) b a≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact endpointPadding_ne_zero (a i) b (ha i)

theorem tuplePadding_degree (b : ℕ) (a : Fin 15 → ℕ) (ha : ∀ i,a i≤b) :
    (tuplePadding (K:=K) b a).natDegree+2*(∑ i,a i)=30*b := by
  rw [tuplePadding,Polynomial.natDegree_prod _ _ (fun i _ => endpointPadding_ne_zero (a i) b (ha i))]
  simp_rw [endpointPadding_degree _ _ (ha _)]
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  have heq : (∑ i : Fin 15, (2*b-2*a i+2*a i))=∑ _i : Fin 15,2*b := by
    apply Finset.sum_congr rfl
    intro i _
    have := ha i
    omega
  rw [heq]
  simp
  omega

theorem pearsonBoundaryNumerator_degree (b : ℕ) (a : Fin 15 → ℕ) (q : K[X])
    (ha : ∀ i,a i≤b) (hq : (q.natDegree:ℤ)+6≤tupleBeta b a) :
    (pearsonBoundaryNumerator b a q).natDegree < ((endpointDenominator (K:=K) b)^10).natDegree := by
  have hp := tuplePadding_degree (K:=K) b a ha
  have hqcomp : (q.comp ((C 2*X+1)^2)).natDegree≤2*q.natDegree := by
    have h := Polynomial.natDegree_comp_le (p:=q) (q:=((C 2*X+1)^2))
    have hd : (((C 2*X+1)^2):K[X]).natDegree=2 := by
      rw [Polynomial.natDegree_pow]
      have hx : (C 2*X+(1:K[X])).natDegree=1 := by
        apply Polynomial.natDegree_eq_of_degree_eq_some
        compute_degree!
      rw [hx]
    rw [hd] at h
    omega
  have hn : (pearsonBoundaryNumerator b a q).natDegree≤
      10+2*q.natDegree+(tuplePadding (K:=K) b a).natDegree := by
    unfold pearsonBoundaryNumerator
    calc
      _ ≤ ((C (2^21:K)*(X-C (b:K))^5*(X+C ((b+1:ℕ):K))^5)*
          q.comp ((C 2*X+1)^2)).natDegree+(tuplePadding (K:=K) b a).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 10+2*q.natDegree+(tuplePadding (K:=K) b a).natDegree := by
        have h₁ := Polynomial.natDegree_mul_le (p:=C (2^21:K)*(X-C (b:K))^5*(X+C ((b+1:ℕ):K))^5)
          (q:=q.comp ((C 2*X+1)^2))
        have h₂ := Polynomial.natDegree_mul_le (p:=C (2^21:K)*(X-C (b:K))^5)
          (q:=(X+C ((b+1:ℕ):K))^5)
        have h₃ := Polynomial.natDegree_mul_le (p:=C (2^21:K)) (q:=(X-C (b:K))^5)
        simp only [Polynomial.natDegree_C,Polynomial.natDegree_pow,
          Polynomial.natDegree_X_sub_C,Polynomial.natDegree_X_add_C] at h₂ h₃
        omega
  rw [Polynomial.natDegree_pow,endpointDenominator_degree]
  unfold tupleBeta at hq
  have hs : (∑ i,(a i:ℤ))=((∑ i,a i:ℕ):ℤ) := by simp
  rw [hs] at hq
  omega

theorem pearsonBoundary_partialFractions (b : ℕ) (a : Fin 15 → ℕ) (q : K[X])
    (ha : ∀ i,a i≤b) (hq : (q.natDegree:ℤ)+6≤tupleBeta b a) :
    ∃ c : ℤ → Fin 10 → K,
      pearsonBoundaryFunction b a q = ∑ j ∈ Finset.Ico (-(b:ℤ)) b,
        ∑ k : Fin 10,c j k • rationalPole (j:K) (k.val+1) := by
  exact integer_partialFractions _ 10 (pearsonBoundaryNumerator b a q)
    (pearsonBoundaryNumerator_degree b a q ha hq)

theorem pearsonBoundary_coeff_zero (b : ℕ) (a : Fin 15 → ℕ) (q : K[X])
    (h : ℕ) (hh : h<5) : rationalCoefficientAt (b:K) h (pearsonBoundaryFunction b a q)=0 := by
  have heq : pearsonBoundaryNumerator b a q = (X-C (b:K))^5 *
      (C (2^21:K)*(X+C ((b+1:ℕ):K))^5*q.comp ((C 2*X+1)^2)*tuplePadding b a) := by
    unfold pearsonBoundaryNumerator
    ring
  unfold pearsonBoundaryFunction
  rw [heq]
  apply rationalCoefficientAt_boundary_factor (b:K) _ _ _ 5 h hh
  simpa using pow_ne_zero 10 (endpointDenominator_eval_boundary (K:=K) b)

end OddZeta.FourValue

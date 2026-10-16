import FourValueCenteredProducts
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! The actual infinite seed tail identity, obtained from a polynomial
antidifference and a proved vanishing boundary term. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial Filter Topology

theorem seedPolynomial_degree {K : Type*} [Field K] [CharZero K] (c : Fin 5 → K) :
    (seedPolynomial c).natDegree≤8 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro h _
  apply (Polynomial.natDegree_smul_le _ _).trans
  have heq : (X*(X-1):K[X]).natDegree=2 := by
    have h := Polynomial.monic_X.natDegree_mul (Polynomial.monic_X_sub_C (1:K))
    rw [Polynomial.natDegree_X,Polynomial.natDegree_X_sub_C] at h
    simpa using h
  rw [Polynomial.natDegree_pow,heq]
  have := h.isLt
  omega

theorem seedTail_step (b : ℕ) (Q : ℝ[X]) (x : ℝ) (hx : (b:ℝ)<x) :
    Q.eval x/(seedTailDenominator b).eval x-
      Q.eval (x+1)/(seedTailDenominator b).eval (x+1) =
      (seedAntidifference (b:ℝ) Q).eval x/(centeredDenominator b).eval x := by
  have hR := seedTailDenominator_eval_ne_zero b x hx
  have hR' := seedTailDenominator_eval_ne_zero b (x+1) (by linarith)
  have hD := centeredDenominator_eval_ne_zero_above b x hx
  have hd₁ : (centeredDenominator b).eval x=(x+b)*(seedTailDenominator b).eval x := by
    rw [seedTailDenominator_factor]
    simp
  have hd₂ : (centeredDenominator b).eval x=(x-b)*(seedTailDenominator b).eval (x+1) := by
    rw [seedTailDenominator_shift_factor]
    simp
  have h₁ : Q.eval x/(seedTailDenominator b).eval x=
      ((x+b)*Q.eval x)/(centeredDenominator b).eval x := by
    apply (div_eq_div_iff hR hD).mpr
    rw [hd₁]
    ring
  have h₂ : Q.eval (x+1)/(seedTailDenominator b).eval (x+1)=
      ((x-b)*Q.eval (x+1))/(centeredDenominator b).eval x := by
    apply (div_eq_div_iff hR' hD).mpr
    rw [hd₂]
    ring
  rw [h₁,h₂,← sub_div]
  congr 1
  simp [seedAntidifference]

theorem seedTail_finite_sum (b : ℕ) (Q : ℝ[X]) (x : ℝ) (hx : (b:ℝ)<x) (N : ℕ) :
    (∑ k ∈ Finset.range N,
      (seedAntidifference (b:ℝ) Q).eval (x+k)/(centeredDenominator b).eval (x+k)) =
      Q.eval x/(seedTailDenominator b).eval x-
        Q.eval (x+N)/(seedTailDenominator b).eval (x+N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ,ih,← seedTail_step b Q (x+N)
        (by have hN : (0:ℝ)≤(N:ℝ) := Nat.cast_nonneg N; linarith)]
      simp only [Nat.cast_add,Nat.cast_one]
      rw [← add_assoc]
      ring

theorem seedTail_boundary_tendsto_zero (b : ℕ) (hb : 5≤b) (Q : ℝ[X])
    (hQ : Q.natDegree≤8) (x : ℝ) :
    Tendsto (fun N : ℕ => Q.eval (x+N)/(seedTailDenominator b).eval (x+N))
      atTop (𝓝 0) := by
  have hdeg : Q.degree<(seedTailDenominator (K:=ℝ) b).degree := by
    apply Polynomial.degree_lt_degree
    rw [seedTailDenominator_degree]
    omega
  have ht := Polynomial.div_tendsto_atTop_zero_of_degree_lt Q (seedTailDenominator b) hdeg
  exact ht.comp (tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop)

theorem seedTail_tendsto_sum (b : ℕ) (hb : 5≤b) (Q : ℝ[X]) (hQ : Q.natDegree≤8)
    (x : ℝ) (hx : (b:ℝ)<x) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
      (seedAntidifference (b:ℝ) Q).eval (x+k)/(centeredDenominator b).eval (x+k))
      atTop (𝓝 (Q.eval x/(seedTailDenominator b).eval x)) := by
  simp_rw [seedTail_finite_sum b Q x hx]
  simpa using tendsto_const_nhds.sub (seedTail_boundary_tendsto_zero b hb Q hQ x)

/-- The seed sum is genuinely an infinite sum, with no assumed boundary
limit. Positivity of the original even-power terms supplies summability. -/
theorem seedTail_hasSum (b : ℕ) (hb : 5≤b) (l : Fin 5) (c : Fin 5 → ℝ)
    (hc : seedAntidifference (b:ℝ) (seedPolynomial c)=(2:ℝ) • X^(2*l.val))
    (x : ℝ) (hx : (b:ℝ)<x) :
    HasSum (fun k : ℕ => 2*(x+k)^(2*l.val)/(centeredDenominator b).eval (x+k))
      ((seedPolynomial c).eval x/(seedTailDenominator b).eval x) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => ?_) _).mpr
  · have h := seedTail_tendsto_sum b hb (seedPolynomial c) (seedPolynomial_degree c) x hx
    simpa [hc,Polynomial.eval_smul] using h
  · apply div_nonneg
    · exact mul_nonneg (by norm_num) (pow_nonneg (by
        have hb0 : (0:ℝ)≤(b:ℝ) := Nat.cast_nonneg b
        have hk0 : (0:ℝ)≤(k:ℝ) := Nat.cast_nonneg k
        linarith) _)
    · exact (centeredDenominator_eval_pos_above b (x+k) (by
        have hk0 : (0:ℝ)≤(k:ℝ) := Nat.cast_nonneg k
        linarith)).le

/-- For every required monomial, an actual rational-function seed tail
and its convergent summation formula exist. -/
theorem seedTail_monomial_exists (b : ℕ) (hb : 5≤b) (l : Fin 5) :
    ∃ c : Fin 5 → ℝ, ∀ x : ℝ, (b:ℝ)<x →
      HasSum (fun k : ℕ => 2*(x+k)^(2*l.val)/(centeredDenominator b).eval (x+k))
        ((seedPolynomial c).eval x/(seedTailDenominator b).eval x) := by
  obtain ⟨c,hc,_⟩ := seedAntidifference_monomial (b:ℝ) (seed_natural_parameter b hb) l
  exact ⟨c,fun x hx => seedTail_hasSum b hb l c hc x hx⟩

end OddZeta.FourValue

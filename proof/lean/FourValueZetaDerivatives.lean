import FourValueTaylorDeriv
import FourValueClassicalZeta
import FourValueSeedPoles

noncomputable section
namespace OddZeta.FourValue
open Polynomial Filter
open scoped Topology

theorem partialFraction_support_of_regular (b : ℕ) (f : RatFunc ℂ)
    (c : ℤ → Fin 10 → ℂ)
    (hf : f=∑ j ∈ poleWindow b,∑ k : Fin 10,c j k • rationalPole (j:ℂ) (k.val+1))
    (p q : ℂ[X]) (hfq : f=algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q)
    (x : ℂ) (hq : q.eval x≠0) : OutsidePoleWindow b c x := by
  intro j hj k
  by_cases heq : x=(j:ℂ)
  · left
    rw [← integer_partialFractions_coefficient _ _ c f hf j hj k,← heq,hfq]
    exact rationalCoefficientAt_regular_neg x p q hq _ (by omega)
  · exact Or.inr heq

/-- Analytic derivatives of the actual polynomial quotient agree with its
formal Laurent coefficients at every regular point. -/
theorem rationalFraction_iteratedDeriv (b : ℕ) (f : RatFunc ℂ)
    (c : ℤ → Fin 10 → ℂ)
    (hf : f=∑ j ∈ poleWindow b,∑ k : Fin 10,c j k • rationalPole (j:ℂ) (k.val+1))
    (p q : ℂ[X]) (hfq : f=algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q)
    (h : ℕ) (x : ℂ) (hq : q.eval x≠0) :
    iteratedDeriv h (fun z : ℂ => p.eval z/q.eval z) x =
      (Nat.factorial h:ℂ)*rationalCoefficientAt x h f := by
  have Hreg : ∀ᶠ y in 𝓝 x,q.eval y≠0 :=
    (q.continuous.continuousAt.eventually_ne hq)
  have Heq : (fun z : ℂ => p.eval z/q.eval z) =ᶠ[𝓝 x] partialFractionValue b c 0 := by
    filter_upwards [Hreg] with y hy
    rw [← rationalCoefficientAt_partialFraction_regular b 0 f c hf y
      (partialFraction_support_of_regular b f c hf p q hfq y hy),hfq]
    exact (rationalCoefficientAt_regular_zero y p q hy).symm
  rw [Heq.iteratedDeriv_eq h,partialFractionValue_iteratedDeriv b c h x
    (partialFraction_support_of_regular b f c hf p q hfq x hq)]
  rw [rationalCoefficientAt_partialFraction_regular b h f c hf x
    (partialFraction_support_of_regular b f c hf p q hfq x hq)]

def targetZetaNumerator (n : ℕ) (p : ℂ[X]) : ℂ[X] :=
  C (targetNormalization (K:=ℂ) n)*
    (tupleNumerator (100*n)*(p.comp (C 4*X)).comp (X^2))

def targetZetaFunction (n : ℕ) (p : ℂ[X]) (z : ℂ) : ℂ :=
  (targetZetaNumerator n p).eval z/(tupleDenominator (targetEndpointTuple n)).eval z

theorem targetZetaTest_fraction (n : ℕ) (p : ℂ[X]) :
    targetZetaTest n p = algebraMap ℂ[X] (RatFunc ℂ) (targetZetaNumerator n p) /
      algebraMap ℂ[X] (RatFunc ℂ) (tupleDenominator (targetEndpointTuple n)) := by
  rw [targetZetaTest,RatFunc.smul_eq_C_mul,tupleRationalTest_fraction,targetZetaNumerator]
  simp only [map_mul,RatFunc.algebraMap_C]
  ring

theorem targetZetaFunction_formula (n : ℕ) (p : ℂ[X]) (z : ℂ) :
    targetZetaFunction n p z = targetNormalization n *
      (2*z*(centeredDenominator (K:=ℂ) (100*n)).eval z^5*p.eval (4*z^2)) /
        (∏ i : Fin 15,(centeredDenominator (K:=ℂ) (targetEndpointTuple n i)).eval z) := by
  simp [targetZetaFunction,targetZetaNumerator,tupleNumerator,tupleDenominator,Polynomial.eval_prod]

theorem targetZetaDenominator_regular (n t : ℕ) (ht : 67*n<t) :
    (tupleDenominator (K:=ℂ) (targetEndpointTuple n)).eval (t:ℂ)≠0 := by
  simp only [tupleDenominator,Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact centeredDenominator_complex_ne_zero_above _ _
    (lt_of_le_of_lt (targetEndpointTuple_le_67 n i) ht)

theorem targetZetaFunction_iteratedDeriv (n : ℕ) (p : ℂ[X])
    (hp : p.natDegree≤361*n+3) (h t : ℕ) (ht : 67*n<t) :
    iteratedDeriv h (targetZetaFunction n p) (t:ℂ)=
      (Nat.factorial h:ℂ)*rationalCoefficientAt (t:ℂ) h (targetZetaTest n p) := by
  obtain ⟨c,hc⟩ := targetZetaTest_partialFractions n p hp
  exact rationalFraction_iteratedDeriv (100*n) _ c hc _ _
    (targetZetaTest_fraction n p) h (t:ℂ) (targetZetaDenominator_regular n t ht)

/-- The intended fourth-derivative series, normalized by 4!=24, converges
to the actual classical-zeta linear form. No interchange of an infinite
sum with differentiation is assumed. -/
theorem classicalZetaFunctional_hasSum_fourthDeriv (n : ℕ) (p : ℂ[X])
    (hp : p.natDegree≤361*n+3) :
    HasSum (fun r : ℕ => iteratedDeriv 4 (targetZetaFunction n p) ((r+67*n+1:ℕ):ℂ)/24)
      (classicalZetaFunctional n p) := by
  apply (classicalZetaFunctional_hasSum n p hp).congr_fun
  intro r
  rw [targetZetaFunction_iteratedDeriv n p hp 4 _ (by omega)]
  norm_num

theorem classicalZetaFunctional_fourthDeriv_tsum (n : ℕ) (p : ℂ[X])
    (hp : p.natDegree≤361*n+3) :
    (∑' r : ℕ, iteratedDeriv 4 (targetZetaFunction n p) ((r+67*n+1:ℕ):ℂ)/24)=
      classicalZetaFunctional n p :=
  (classicalZetaFunctional_hasSum_fourthDeriv n p hp).tsum_eq

end OddZeta.FourValue

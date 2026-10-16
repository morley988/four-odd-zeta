import FourValueConcretePearson
import FourValueSeedTail

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem seedTailDenominator_taylor_one (b : ℕ) :
    (seedTailDenominator (K:=K) b).taylor 1=endpointDenominator b := by
  apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero (b:K))
  rw [← centeredDenominator_endpoint_factor,seedTailDenominator_shift_factor]
  simp [Polynomial.taylor_apply]

def seedBoundaryFunction (b : ℕ) (Q : K[X]) : RatFunc K :=
  -algebraMap K[X] (RatFunc K) (Q.taylor 1) /
    algebraMap K[X] (RatFunc K) (endpointDenominator b)

theorem seedBoundaryFunction_difference (b : ℕ) (Q : K[X]) :
    rationalDifference (seedBoundaryFunction b Q) =
      algebraMap K[X] (RatFunc K) (seedAntidifference (b:K) Q) /
        algebraMap K[X] (RatFunc K) (centeredDenominator b) := by
  have hR := RatFunc.algebraMap_ne_zero (K:=K) (seedTailDenominator_monic (K:=K) b).ne_zero
  have hE := RatFunc.algebraMap_ne_zero (K:=K) (endpointDenominator_monic (K:=K) b).ne_zero
  have hD := RatFunc.algebraMap_ne_zero (K:=K) (centeredDenominator_monic (K:=K) b).ne_zero
  have hs : rationalShift (-1:K) (seedBoundaryFunction b Q) =
      -algebraMap K[X] (RatFunc K) Q / algebraMap K[X] (RatFunc K) (seedTailDenominator b) := by
    rw [seedBoundaryFunction,← seedTailDenominator_taylor_one]
    rw [neg_div,map_neg,rationalShift_fraction]
    simp only [
      Polynomial.taylor_taylor,neg_add_cancel,Polynomial.taylor_zero,map_neg,neg_div]
  rw [rationalDifference_apply,hs,seedBoundaryFunction]
  have h₁ := congrArg (algebraMap K[X] (RatFunc K)) (seedTailDenominator_factor (K:=K) b)
  have h₂ := congrArg (algebraMap K[X] (RatFunc K)) (centeredDenominator_endpoint_factor (K:=K) b)
  simp only [map_mul] at h₁ h₂
  change _ = algebraMap K[X] (RatFunc K)
    ((X+C (b:K))*Q-(X-C (b:K))*Q.comp (X+1)) / _
  have ht : Q.comp (X+1)=Q.taylor 1 := by simp [Polynomial.taylor_apply]
  rw [ht, map_sub,map_mul,map_mul]
  apply (eq_div_iff hD).mpr
  rw [sub_mul,div_mul_eq_mul_div,div_mul_eq_mul_div]
  conv_lhs => lhs; rw [h₂]
  conv_lhs => rhs; rw [h₁]
  field_simp
  <;> ring

theorem seedBoundaryFunction_partialFractions (b : ℕ) (hb : 5≤b) (Q : K[X])
    (hQ : Q.natDegree≤8) :
    ∃ c : ℤ → Fin 1 → K, seedBoundaryFunction b Q=
      ∑ j ∈ Finset.Ico (-(b:ℤ)) b,∑ k : Fin 1,c j k • rationalPole (j:K) (k.val+1) := by
  have hp : (-(Q.taylor 1)).natDegree <
      ((integerRootProduct (K:=K) (Finset.Ico (-(b:ℤ)) b))^1).natDegree := by
    rw [Polynomial.natDegree_neg,Polynomial.natDegree_taylor,pow_one]
    change Q.natDegree < (endpointDenominator (K:=K) b).natDegree
    rw [endpointDenominator_degree]
    omega
  simpa [seedBoundaryFunction,map_neg,endpointDenominator] using
    integer_partialFractions (Finset.Ico (-(b:ℤ)) b) 1 (-(Q.taylor 1)) hp

theorem seedBoundaryFunction_B (b : ℕ) (hb : 5≤b) (Q : K[X])
    (hQ : Q.natDegree≤8) (l : ℕ) (hl : 0<l) :
    rationalB b l (rationalDifference (seedBoundaryFunction b Q))=0 := by
  obtain ⟨c,hc⟩ := seedBoundaryFunction_partialFractions b hb Q hQ
  let L := (rationalB (K:=K) b l).comp rationalDifference
  change L (seedBoundaryFunction b Q)=0
  rw [hc,map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Fin.sum_univ_one,map_smul]
  change c j 0 • rationalB b l (rationalDifference (rationalPole (j:K) 1))=0
  rw [rationalDifference_apply,rationalB_pole_difference b j hj 1 l hl,smul_zero]

theorem seedBoundaryFunction_C (b : ℕ) (hb : 5≤b) (Q : K[X])
    (hQ : Q.natDegree≤8) (h : ℕ) :
    rationalC b h (rationalDifference (seedBoundaryFunction b Q)) =
      rationalCoefficientAt (b:K) h
        (algebraMap K[X] (RatFunc K) (Q.taylor 1) /
          algebraMap K[X] (RatFunc K) (endpointDenominator b)) := by
  obtain ⟨c,hc⟩ := seedBoundaryFunction_partialFractions b hb Q hQ
  let L := (rationalC (K:=K) b h).comp rationalDifference + rationalCoefficientAt (b:K) h
  have hz : L (seedBoundaryFunction b Q)=0 := by
    rw [hc,map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Fin.sum_univ_one,map_smul]
    have hz : L (rationalPole (j:K) 1)=0 := by
      change rationalC b h (rationalDifference (rationalPole (j:K) 1)) + _=0
      rw [rationalDifference_apply,rationalC_pole_difference b h j hj 0 (by omega),neg_add_cancel]
    simpa only [Fin.val_zero,zero_add,hz,smul_zero]
  change rationalC b h (rationalDifference (seedBoundaryFunction b Q)) +
    rationalCoefficientAt (b:K) h (seedBoundaryFunction b Q)=0 at hz
  simpa [seedBoundaryFunction,neg_div,map_neg] using eq_neg_of_add_eq_zero_left hz

end OddZeta.FourValue

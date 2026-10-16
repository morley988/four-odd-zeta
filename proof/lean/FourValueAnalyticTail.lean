import FourValueAnalyticCoordinates
import FourValueContourRays

noncomputable section
namespace OddZeta.FourValue
open Polynomial

theorem analyticZetaFunction_gap_fourthDeriv (n t : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) (ht : 67*n<t) (ht' : t≤100*n) :
    iteratedDeriv 4 (analyticZetaFunction n P) (t:ℂ)=0 := by
  unfold analyticZetaFunction
  rw [targetZetaFunction_iteratedDeriv n (analyticCoordinate P)
    (by simpa [analyticCoordinate_natDegree] using hP) 4 t ht]
  rw [targetZetaTest_gap_zero n t ht ht' _ 4 (by norm_num),mul_zero]

theorem analyticZetaFunctional_hasSum_after_contour (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) :
    HasSum (fun r : ℕ => iteratedDeriv 4 (analyticZetaFunction n P) ((r+100*n+1:ℕ):ℂ)/24)
      (analyticZetaFunctional n P) := by
  have h := analyticZetaFunctional_hasSum n P hP
  have hz : (∑ r∈Finset.range (33*n),
      iteratedDeriv 4 (analyticZetaFunction n P) ((r+67*n+1:ℕ):ℂ)/24)=0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [analyticZetaFunction_gap_fourthDeriv n _ P hP (by omega) (by
      have := Finset.mem_range.mp hr
      omega),zero_div]
  have ht := (hasSum_nat_add_iff' (33*n)).mpr h
  simp only [hz,sub_zero] at ht
  apply ht.congr_fun
  intro r
  rw [show r+33*n+67*n+1=r+100*n+1 by omega]
end OddZeta.FourValue

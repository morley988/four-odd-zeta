import FourValueConcreteMassInterpolation
import FourValueAnalyticDeterminants
import FourValueContourConvergence

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory

def adaptedIndexMass (n i : ℕ) : ℝ := (i:ℝ)/(100*n:ℕ)
def adaptedWeights (n i : ℕ) : Fin 45→ℝ := concreteBasisWeight (adaptedIndexMass n i)

theorem adaptedIndexMass_bounds (n i : ℕ) (hn : 1≤n) (hi : i≤targetHankelDegree n) :
    0≤adaptedIndexMass n i ∧ adaptedIndexMass n i≤basisLimit := by
  have hnR : (0:ℝ)<(100*n:ℕ) := by exact_mod_cast (show 0<100*n by omega)
  have hiN : 2*i≤361*n := by unfold targetHankelDegree at hi; omega
  have hiR : 2*(i:ℝ)≤361*(n:ℝ) := by exact_mod_cast hiN
  unfold adaptedIndexMass basisLimit
  constructor
  · positivity
  · apply (div_le_iff₀ hnR).mpr
    push_cast
    linarith

theorem adaptedWeights_nonneg (n i : ℕ) (hn : 1≤n) (hi : i≤targetHankelDegree n) (l : Fin 45) :
    0≤adaptedWeights n i l :=
  concreteBasisWeight_nonneg _ (adaptedIndexMass_bounds n i hn hi).1 (adaptedIndexMass_bounds n i hn hi).2 l

theorem adaptedWeights_sum (n i : ℕ) (hn : 1≤n) (hi : i≤targetHankelDegree n) :
    ∑ l,adaptedWeights n i l=1 :=
  concreteBasisWeight_sum _ (adaptedIndexMass_bounds n i hn hi).1 (adaptedIndexMass_bounds n i hn hi).2

def actualAdaptedBasis (n i : ℕ) : ℂ[X] :=
  scaledAnalyticBasis (100*n:ℕ) i (adaptedWeights n i)

theorem actualAdaptedBasis_natDegree (n i : ℕ) (hn : 1≤n) (hi : i≤targetHankelDegree n) :
    (actualAdaptedBasis n i).natDegree=i :=
  scaledAnalyticBasis_natDegree _ (by exact_mod_cast (show 100*n≠0 by omega)) i _
    (adaptedWeights_nonneg n i hn hi) (adaptedWeights_sum n i hn hi)

theorem actualAdaptedBasis_leadingCoeff (n i : ℕ) (hn : 1≤n) (hi : i≤targetHankelDegree n) :
    (actualAdaptedBasis n i).leadingCoeff=1/(Nat.factorial (2*i):ℂ) :=
  scaledAnalyticBasis_leadingCoeff _ (by exact_mod_cast (show 100*n≠0 by omega)) i _
    (adaptedWeights_nonneg n i hn hi) (adaptedWeights_sum n i hn hi)

theorem actualAdaptedBasis_product_degree (n i j : ℕ) (hn : 1≤n)
    (hi : i≤targetHankelDegree n) (hj : j≤targetHankelDegree n) :
    (actualAdaptedBasis n i*actualAdaptedBasis n j).natDegree≤361*n+3 := by
  have hd := natDegree_mul_le (p:=actualAdaptedBasis n i) (q:=actualAdaptedBasis n j)
  rw [actualAdaptedBasis_natDegree n i hn hi,actualAdaptedBasis_natDegree n j hn hj] at hd
  unfold targetHankelDegree at hi hj
  omega

def actualAdaptedZetaMatrix (n : ℕ) :
    Matrix (Fin (targetHankelDegree n+1)) (Fin (targetHankelDegree n+1)) ℂ :=
  fun i j => analyticZetaFunctional n (actualAdaptedBasis n i.val*actualAdaptedBasis n j.val)

theorem actualAdaptedZetaMatrix_rank (n : ℕ) (hn : 1≤n) :
    (actualAdaptedZetaMatrix n).rank=(momentHankel (analyticZetaFunctional n) (targetHankelDegree n)).rank := by
  have hw := fun i : Fin (targetHankelDegree n+1) => adaptedWeights_nonneg n i.val hn (by omega)
  have hs := fun i : Fin (targetHankelDegree n+1) => adaptedWeights_sum n i.val hn (by omega)
  have hM : ((100*n:ℕ):ℝ)≠0 := by exact_mod_cast (show 100*n≠0 by omega)
  have hd := scaledAnalyticCoefficientMatrix_det_ne_zero _ hM (targetHankelDegree n)
    (fun i => adaptedWeights n i.val) hw hs
  have he := momentGram_change_of_basis (analyticZetaFunctional n) (targetHankelDegree n)
    (fun i => actualAdaptedBasis n i.val) (fun i => by rw [actualAdaptedBasis_natDegree n i.val hn (by omega)]; omega)
  change (polynomialCoefficientMatrix (targetHankelDegree n) (fun i => actualAdaptedBasis n i.val)).det≠0 at hd
  change actualAdaptedZetaMatrix n=_ at he
  rw [he,Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hd,
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ (by simpa only [Matrix.det_transpose] using hd)]

theorem actualAdaptedZetaMatrix_nonzero_minor (n : ℕ) (hn : 1≤n) :
    ∃ rows cols : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1),
      ((actualAdaptedZetaMatrix n).submatrix rows cols).det≠0 := by
  apply rank_selects_nonzero_minor
  rw [actualAdaptedZetaMatrix_rank n hn]
  change _≤(momentHankel (analyticFunctional (classicalZetaFunctional n)) _).rank
  rw [analyticFunctional_momentHankel_rank,← squareBasisGram_rank]
  exact (classicalZeta_uniform_nonvanishing n hn).1

theorem actualAdaptedZetaMatrix_hasSum (n : ℕ) (hn : 1≤n)
    (i j : Fin (targetHankelDegree n+1)) :
    HasSum (fun r : ℕ => iteratedDeriv 4 (analyticZetaFunction n
      (actualAdaptedBasis n i.val*actualAdaptedBasis n j.val)) ((r+100*n+1:ℕ):ℂ)/24)
      (actualAdaptedZetaMatrix n i j) :=
  analyticZetaFunctional_hasSum_after_contour n _
    (actualAdaptedBasis_product_degree n i.val j.val hn (by omega) (by omega))

theorem actualAdaptedBasis_contour_integrable (n : ℕ) (hn : 1≤n)
    (i j : Fin (targetHankelDegree n+1)) :
    IntegrableOn (fun t : ℝ => analyticZetaFunction n
      (actualAdaptedBasis n i.val*actualAdaptedBasis n j.val) (lowerContourRay n t)*
      contourKernel (lowerContourRay n t)*(3/5-Complex.I)) (Set.Ioi 0) ∧
    IntegrableOn (fun t : ℝ => analyticZetaFunction n
      (actualAdaptedBasis n i.val*actualAdaptedBasis n j.val) (upperContourRay n t)*
      contourKernel (upperContourRay n t)*(3/5+Complex.I)) (Set.Ioi 0) :=
  analyticContourIntegral_integrable n _
    (actualAdaptedBasis_product_degree n i.val j.val hn (by omega) (by omega))
end OddZeta.FourValue

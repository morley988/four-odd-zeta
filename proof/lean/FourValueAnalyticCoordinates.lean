import FourValueConcreteArithmeticComplete

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- Undo X=4Y before evaluating the already checked physical functional. -/
def analyticCoordinate (P : K[X]) : K[X] := P.comp (C (1/4:K)*X)

theorem analyticCoordinate_cancel (P : K[X]) :
    (analyticCoordinate P).comp (C 4*X)=P := by
  simp only [analyticCoordinate,comp_assoc,mul_comp,C_comp,X_comp]
  have h : C (1/4:K)*(C 4*X)=X := by rw [← mul_assoc,← map_mul]; norm_num
  rw [h,comp_X]

theorem analyticCoordinate_natDegree (P : K[X]) : (analyticCoordinate P).natDegree=P.natDegree := by
  unfold analyticCoordinate
  rw [natDegree_comp,natDegree_C_mul_X _ (by norm_num : (1/4:K)≠0),mul_one]

def analyticFunctional (L : K[X] →ₗ[K] K) : K[X] →ₗ[K] K where
  toFun P := L (analyticCoordinate P)
  map_add' P Q := by simp [analyticCoordinate,add_comp]
  map_smul' c P := by simp [analyticCoordinate,smul_comp]

theorem analyticFunctional_moment (L : K[X] →ₗ[K] K) (j : ℕ) :
    analyticFunctional L (X^j)=(1/4:K)^j*L (X^j) := by
  simp only [analyticFunctional, LinearMap.coe_mk, AddHom.coe_mk, analyticCoordinate, pow_comp, X_comp]
  rw [mul_pow, ← map_pow, ← smul_eq_C_mul, map_smul, smul_eq_mul]

theorem analyticFunctional_momentHankel (L : K[X] →ₗ[K] K) (m : ℕ) :
    momentHankel (analyticFunctional L) m =
      Matrix.diagonal (fun i : Fin (m+1) => (1/4:K)^i.val) * momentHankel L m *
      Matrix.diagonal (fun i : Fin (m+1) => (1/4:K)^i.val) := by
  ext i j
  simp only [momentHankel, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [analyticFunctional_moment, pow_add]
  ring

theorem analyticFunctional_momentHankel_rank (L : K[X] →ₗ[K] K) (m : ℕ) :
    (momentHankel (analyticFunctional L) m).rank=(momentHankel L m).rank := by
  have hd : (Matrix.diagonal (fun i : Fin (m+1) => (1/4:K)^i.val)).det≠0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (by norm_num))
  rw [analyticFunctional_momentHankel,Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hd,
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hd]

def analyticZetaFunctional (n : ℕ) : ℂ[X] →ₗ[ℂ] ℂ :=
  analyticFunctional (classicalZetaFunctional n)

def analyticZetaFunction (n : ℕ) (P : ℂ[X]) : ℂ → ℂ :=
  targetZetaFunction n (analyticCoordinate P)

theorem analyticZetaFunction_formula (n : ℕ) (P : ℂ[X]) (z : ℂ) :
    analyticZetaFunction n P z=targetNormalization n *
      (2*z*(centeredDenominator (K:=ℂ) (100*n)).eval z^5*P.eval (z^2)) /
      (∏ i : Fin 15,(centeredDenominator (K:=ℂ) (targetEndpointTuple n i)).eval z) := by
  rw [analyticZetaFunction,targetZetaFunction_formula]
  simp [analyticCoordinate]

theorem analyticZetaFunctional_hasSum (n : ℕ) (P : ℂ[X]) (hP : P.natDegree≤361*n+3) :
    HasSum (fun r : ℕ => iteratedDeriv 4 (analyticZetaFunction n P) ((r+67*n+1:ℕ):ℂ)/24)
      (analyticZetaFunctional n P) := by
  exact classicalZetaFunctional_hasSum_fourthDeriv n (analyticCoordinate P)
    (by simpa [analyticCoordinate_natDegree] using hP)

def analyticZetaMatrix (n : ℕ) := squareBasisGram (analyticZetaFunctional n) (targetHankelDegree n)

theorem analyticZetaMatrix_nonzero_minor (n : ℕ) (hn : 1≤n) :
    ∃ rows cols : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1),
      ((analyticZetaMatrix n).submatrix rows cols).det≠0 := by
  apply rank_selects_nonzero_minor
  rw [analyticZetaMatrix,squareBasisGram_rank]
  change _≤(momentHankel (analyticFunctional (classicalZetaFunctional n)) _).rank
  rw [analyticFunctional_momentHankel_rank,← squareBasisGram_rank]
  exact (classicalZeta_uniform_nonvanishing n hn).1
end OddZeta.FourValue

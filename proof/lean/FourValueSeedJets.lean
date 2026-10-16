import FourValueSeedSystem
import FourValueLaurentAtoms

noncomputable section
namespace OddZeta.FourValue
open Polynomial
open scoped LaurentSeries PowerSeries RatFunc
variable {K : Type*} [Field K] [CharZero K]

theorem rational_regular_zero_jets (a : K) (p q : K[X]) (hq : q.eval a≠0)
    (n : ℕ) (hz : ∀ h<n, rationalCoefficientAt a h
      (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q)=0) :
    ∀ h<n, (p.taylor a).coeff h=0 := by
  let P : K⟦X⟧ := (p.taylor a : K[X])
  let Q : K⟦X⟧ := (q.taylor a : K[X])
  have hQ : PowerSeries.constantCoeff Q≠0 := by
    simpa [Q,Polynomial.constantCoeff_coe,Polynomial.taylor_coeff_zero] using hq
  have hd : (PowerSeries.X:K⟦X⟧)^n ∣ P*Q⁻¹ := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro h hh
    have hzero := hz h hh
    change (rationalLaurentAt a _).coeff _=0 at hzero
    rw [rationalLaurentAt_regular a p q hq,LaurentSeries.coeff_coe_powerSeries] at hzero
    exact hzero
  have hp : (PowerSeries.X:K⟦X⟧)^n ∣ P := by
    have hh := dvd_mul_of_dvd_left hd Q
    rwa [mul_assoc,PowerSeries.inv_mul_cancel Q hQ,mul_one] at hh
  intro h hh
  simpa only [P,Polynomial.coeff_coe] using (PowerSeries.X_pow_dvd_iff.mp hp) h hh

def seedTranslationMatrix (d : K) : Matrix (Fin 5) (Fin 5) K :=
  !![1,d,d^2,d^3,d^4;
     0,1,2*d,3*d^2,4*d^3;
     0,0,1,3*d,6*d^2;
     0,0,0,1,4*d;
     0,0,0,0,1]

theorem seedTranslationMatrix_det (d : K) : (seedTranslationMatrix d).det=1 := by
  have ht : (seedTranslationMatrix d).IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [seedTranslationMatrix]
  rw [Matrix.det_of_isUpperTriangular ht]
  norm_num [seedTranslationMatrix,Fin.prod_univ_succ]

set_option maxHeartbeats 4000000 in
theorem seed_quadratic_jet_factor (c d : K) (i j : Fin 5) :
    ((X^2+C c*X+C d)^j.val : K[X]).coeff i.val =
      (seedJetMatrix c * seedTranslationMatrix d) i j := by
  fin_cases i <;> fin_cases j
  all_goals norm_num [seedJetMatrix,seedTranslationMatrix,Matrix.mul_apply,Fin.sum_univ_succ,
    pow_succ,Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ,Polynomial.coeff_one,Polynomial.coeff_X,Polynomial.coeff_C]
  all_goals ring

theorem seedPolynomial_taylor_jet (b : K) (v : Fin 5 → K) (i : Fin 5) :
    ((seedPolynomial v).taylor (b+1)).coeff i.val =
      ((seedJetMatrix (2*b+1)*seedTranslationMatrix (b*(b+1))).mulVec v) i := by
  have hp : ((X*(X-1):K[X]).taylor (b+1))=X^2+C (2*b+1)*X+C (b*(b+1)) := by
    simp [Polynomial.taylor_mul,Polynomial.taylor_X,map_sub,Polynomial.taylor_one,
      map_add,map_mul,map_ofNat]
    ring
  simp only [seedPolynomial,map_sum,map_smul,Polynomial.taylor_pow,hp,
    Polynomial.finsetSum_coeff,Polynomial.coeff_smul,smul_eq_mul,
    seed_quadratic_jet_factor,Matrix.mulVec,dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem seedPolynomial_zero_of_jets (b : ℕ) (v : Fin 5 → K)
    (hz : ∀ i : Fin 5, ((seedPolynomial v).taylor ((b:K)+1)).coeff i.val=0) :
    v=0 := by
  have hm : IsUnit (seedJetMatrix (2*(b:K)+1)*seedTranslationMatrix ((b:K)*(b+1))) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_mul,seedTranslationMatrix_det,mul_one]
    exact (seed_actual_jet_matrix_nonzero (K:=K) b).isUnit
  apply (Matrix.mulVec_injective_iff_isUnit.mpr hm)
  funext i
  rw [Matrix.mulVec_zero,Pi.zero_apply,← seedPolynomial_taylor_jet]
  exact hz i

end OddZeta.FourValue

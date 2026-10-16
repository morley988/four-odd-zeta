import FourValueAnalyticRounding
import FourValueCertificate

noncomputable section
namespace OddZeta.FourValue
open Polynomial

def analyticCenter (l : Fin 45) : ℂ :=
  let c := Certificate.centers.get ⟨l.val,by simpa [Certificate.center_count] using l.isLt⟩
  (c.1:ℂ)+(c.2:ℂ)*Complex.I

theorem analyticCenter_bound (l : Fin 45) :
    ‖analyticCenter l‖+(1/50:ℝ)≤14697/5000 := by
  let c := Certificate.centers.get ⟨l.val,by simpa [Certificate.center_count] using l.isLt⟩
  have hc := Certificate.root_disk_bounds c (List.get_mem _ _)
  have hc' : |(c.1:ℝ)|+|(c.2:ℝ)|+(1/50:ℝ)≤14697/5000 := by
    have hc0 := (Rat.cast_le (K := ℝ)).mpr hc
    push_cast at hc0
    exact hc0
  have hn := Complex.norm_le_abs_re_add_abs_im (analyticCenter l)
  have hre : (analyticCenter l).re=(c.1:ℝ) := by simp [analyticCenter,c]
  have him : (analyticCenter l).im=(c.2:ℝ) := by simp [analyticCenter,c]
  rw [hre,him] at hn
  linarith

def concreteAnalyticBasis (i : ℕ) (w : Fin 45→ℝ) : ℂ[X] :=
  roundedAnalyticBasis analyticCenter (1/50) i w

theorem concreteAnalyticBasis_monic (i : ℕ) (w : Fin 45→ℝ) :
    (concreteAnalyticBasis i w).Monic := roundedAnalyticBasis_monic _ _ _ _

theorem concreteAnalyticBasis_natDegree (i : ℕ) (w : Fin 45→ℝ)
    (hw : ∀ l,0≤w l) (hs : ∑ l,w l=1) :
    (concreteAnalyticBasis i w).natDegree=i := roundedAnalyticBasis_natDegree _ _ _ _ hw hs

theorem concreteAnalyticBasis_root_bound (i : ℕ) (w : Fin 45→ℝ) (z : ℂ)
    (hz : (concreteAnalyticBasis i w).eval z=0) : ‖z‖≤14697/5000 :=
  roundedAnalyticBasis_root_bound _ _ _ _ _ (by norm_num) (by norm_num) analyticCenter_bound z hz

theorem concreteAnalyticBasis_remainder_lt (i : ℕ) (w : Fin 45→ℝ)
    (hw : ∀ l,0≤w l) (hs : ∑ l,w l=1) : roundedRemainder i w<90 := by
  simpa using roundedRemainder_lt i w hw hs

theorem concreteAnalyticBasis_eval_bound (i : ℕ) (w : Fin 45→ℝ) (z : ℂ) :
    ‖(concreteAnalyticBasis i w).eval z‖ ≤
      ‖z-1‖^(roundedRemainder i w)*4^45*
      ∏ l : Fin 45, ((max ‖z-analyticCenter l‖ (1/50))*
        (max ‖z-star (analyticCenter l)‖ (1/50)))^(roundedBlockSize i w l) := by
  simpa [concreteAnalyticBasis,roundedAnalyticBasis] using
    analyticBasisPolynomial_eval_bound analyticCenter (1/50) (roundedBlockSize i w)
      (roundedRemainder i w) (by norm_num) z

/-- Exact physical scaling; the factorial is kept explicit. -/
def scaledAnalyticBasis (M : ℝ) (i : ℕ) (w : Fin 45→ℝ) : ℂ[X] :=
  C ((M:ℂ)^(2*i)/(Nat.factorial (2*i):ℂ)) *
    (concreteAnalyticBasis i w).comp (C ((M:ℂ)^2)⁻¹*X)

theorem scaledAnalyticBasis_eval (M : ℝ) (hM : M≠0) (i : ℕ) (w : Fin 45→ℝ) (Z : ℂ) :
    (scaledAnalyticBasis M i w).eval ((M:ℂ)^2*Z)=
      ((M:ℂ)^(2*i)/(Nat.factorial (2*i):ℂ))*(concreteAnalyticBasis i w).eval Z := by
  have hMc : (M:ℂ)≠0 := by exact_mod_cast hM
  simp [scaledAnalyticBasis,eval_comp,mul_assoc,hMc]

theorem scaledAnalyticBasis_norm (M : ℝ) (hM : 0<M) (i : ℕ) (w : Fin 45→ℝ) (Z : ℂ) :
    ‖(scaledAnalyticBasis M i w).eval ((M:ℂ)^2*Z)‖=
      M^(2*i)/(Nat.factorial (2*i):ℝ)*‖(concreteAnalyticBasis i w).eval Z‖ := by
  rw [scaledAnalyticBasis_eval M (ne_of_gt hM),norm_mul,norm_div,norm_pow]
  simp [abs_of_pos hM]
end OddZeta.FourValue

import FourValueRectangleResidue
import FourValueContourVerticalLimits

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory

theorem horizontalContourIntegral_translate (n k : ℕ) (P : ℂ[X]) (T : ℝ) :
    (∫ x in (-(1/2):ℝ)..(1/2),analyticZetaFunction n P ((k:ℂ)+(x:ℂ)+(T:ℂ)*Complex.I)*
      contourKernel ((k:ℂ)+(x:ℂ)+(T:ℂ)*Complex.I))=
    ∫ x in ((k:ℝ)-1/2)..((k:ℝ)+1/2),horizontalContourIntegrand n P T x := by
  have h := intervalIntegral.integral_comp_add_left (horizontalContourIntegrand n P T)
    (a:=-(1/2:ℝ)) (b:=1/2) (k:ℝ)
  calc
    _ = ∫ x in (-(1/2):ℝ)..(1/2),horizontalContourIntegrand n P T ((k:ℝ)+x) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [horizontalContourIntegrand,Complex.ofReal_add,Complex.ofReal_natCast]
    _ = _ := by simpa only [sub_eq_add_neg,add_comm] using h

theorem poleRectangleBoundary_vertical_coordinates (n k : ℕ) (P : ℂ[X]) (hk : 1≤k) (T : ℝ) :
    poleRectangleBoundary (fun z => analyticZetaFunction n P z*contourKernel z) (k:ℂ) (1/2) T=
    (∫ x in ((k:ℝ)-1/2)..((k:ℝ)+1/2),horizontalContourIntegrand n P (-T) x)-
    (∫ x in ((k:ℝ)-1/2)..((k:ℝ)+1/2),horizontalContourIntegrand n P T x)+
    (∫ t in -T..T,verticalContourIntegrand n P k t*Complex.I)-
    (∫ t in -T..T,verticalContourIntegrand n P (k-1) t*Complex.I) := by
  have hright (t : ℝ) : (k:ℂ)+(1/2:ℂ)+(t:ℂ)*Complex.I=verticalContourLine k t := by
    simp [verticalContourLine]; ring
  have hleft (t : ℝ) : (k:ℂ)-(1/2:ℂ)+(t:ℂ)*Complex.I=verticalContourLine (k-1:ℕ) t := by
    simp [verticalContourLine,Nat.cast_sub hk]; ring
  unfold poleRectangleBoundary
  have hb : (∫ x in (-(1/2):ℝ)..(1/2),analyticZetaFunction n P ((k:ℂ)+(x:ℂ)-(T:ℂ)*Complex.I)*
      contourKernel ((k:ℂ)+(x:ℂ)-(T:ℂ)*Complex.I))=
    ∫ x in ((k:ℝ)-1/2)..((k:ℝ)+1/2),horizontalContourIntegrand n P (-T) x := by
    simpa only [Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using horizontalContourIntegral_translate n k P (-T)
  rw [hb,horizontalContourIntegral_translate]
  push_cast
  simp_rw [hright,hleft]
  simp only [verticalContourIntegrand,intervalIntegral.integral_mul_const]
  ring
end OddZeta.FourValue

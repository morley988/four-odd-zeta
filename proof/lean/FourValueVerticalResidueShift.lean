import FourValueRectangleCoordinates

noncomputable section
namespace OddZeta.FourValue
open Polynomial MeasureTheory Filter
open scoped Topology

theorem verticalContourIntegral_adjacent (n k : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) (hk : 100*n<k) :
    verticalContourIntegral n P k-verticalContourIntegral n P (k-1)=
      (2*(Real.pi:ℂ)*Complex.I/24)*iteratedDeriv 4 (analyticZetaFunction n P) (k:ℂ) := by
  have hcast : ((100*n+1:ℕ):ℝ)≤k := by exact_mod_cast hk
  have hhor := horizontalContourIntegral_fixed_closing n P hP ((k:ℝ)-1/2) ((k:ℝ)+1/2)
    (by push_cast at hcast ⊢; linarith) (by linarith)
  have hvR := verticalContourIntegral_truncation n k P hP (by omega)
  have hvL := verticalContourIntegral_truncation n (k-1) P hP (by omega)
  have hlim := (((hhor.2.sub hhor.1).add hvR).sub hvL)
  simp only [sub_zero,zero_sub,zero_add] at hlim
  have hconst : Tendsto (fun T : ℝ =>
      (∫ x in ((k:ℝ)-1/2)..((k:ℝ)+1/2),horizontalContourIntegrand n P (-T) x)-
      (∫ x in ((k:ℝ)-1/2)..((k:ℝ)+1/2),horizontalContourIntegrand n P T x)+
      (∫ t in -T..T,verticalContourIntegrand n P k t*Complex.I)-
      (∫ t in -T..T,verticalContourIntegrand n P (k-1) t*Complex.I)) atTop
      (𝓝 ((2*(Real.pi:ℂ)*Complex.I/24)*iteratedDeriv 4 (analyticZetaFunction n P) (k:ℂ))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    rw [← poleRectangleBoundary_vertical_coordinates n k P (by omega) T,
      analyticContour_rectangle_residue n k P hk T (by linarith)]
  exact tendsto_nhds_unique hlim hconst

theorem verticalContourIntegral_finite_shift (n N : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) :
    (∑ j∈Finset.range N,(2*(Real.pi:ℂ)*Complex.I/24)*
      iteratedDeriv 4 (analyticZetaFunction n P) ((j+100*n+1:ℕ):ℂ))=
      verticalContourIntegral n P (100*n+N)-verticalContourIntegral n P (100*n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    have h := verticalContourIntegral_adjacent n (100*n+N+1) P hP (by omega)
    have he : 100*n+N+1-1=100*n+N := by omega
    rw [he] at h
    have hi : N+100*n+1=100*n+N+1 := by omega
    rw [hi,← h]
    congr 1 <;> simp only [Nat.succ_eq_add_one,Nat.add_assoc] <;> ring

theorem analyticZetaFunctional_eq_vertical (n : ℕ) (P : ℂ[X])
    (hP : P.natDegree≤361*n+3) :
    (2*(Real.pi:ℂ)*Complex.I)*analyticZetaFunctional n P= -verticalContourIntegral n P (100*n) := by
  have hs := (analyticZetaFunctional_hasSum_after_contour n P hP).mul_left (2*(Real.pi:ℂ)*Complex.I)
  have hs' : HasSum (fun j : ℕ => (2*(Real.pi:ℂ)*Complex.I/24)*
      iteratedDeriv 4 (analyticZetaFunction n P) ((j+100*n+1:ℕ):ℂ))
      ((2*(Real.pi:ℂ)*Complex.I)*analyticZetaFunctional n P) := by
    apply hs.congr_fun
    intro j
    ring
  have hsum := hs'.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hv := (verticalContourIntegral_far_tendsto_zero n P hP).sub_const (verticalContourIntegral n P (100*n))
  simp only [zero_sub] at hv
  have he : (fun N : ℕ => ∑ j∈Finset.range (N+1),(2*(Real.pi:ℂ)*Complex.I/24)*
      iteratedDeriv 4 (analyticZetaFunction n P) ((j+100*n+1:ℕ):ℂ))=
      (fun N : ℕ => verticalContourIntegral n P (100*n+N+1)-verticalContourIntegral n P (100*n)) := by
    funext N
    simpa only [Nat.add_assoc] using verticalContourIntegral_finite_shift n (N+1) P hP
  change Tendsto (fun N : ℕ => ∑ j∈Finset.range (N+1),(2*(Real.pi:ℂ)*Complex.I/24)*
      iteratedDeriv 4 (analyticZetaFunction n P) ((j+100*n+1:ℕ):ℂ)) atTop _ at hsum
  rw [he] at hsum
  exact tendsto_nhds_unique hsum hv
end OddZeta.FourValue

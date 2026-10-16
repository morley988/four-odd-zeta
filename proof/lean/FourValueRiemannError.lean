import FourValueUniformLaplace

noncomputable section
namespace OddZeta.FourValue
open MeasureTheory Set

theorem uniform_grid_integral_error (f : ℝ→ℝ) (M : ℝ) (hM : 0<M) (N : ℕ) (ε : ℝ)
    (hf : ContinuousOn f (Icc 0 ((N:ℝ)/M)))
    (hmod : ∀ j : ℕ,j<N → ∀ x ∈ Icc ((j:ℝ)/M) (((j:ℝ)+1)/M),|f ((j:ℝ)/M)-f x|≤ε) :
    |(1/M)*(∑ j∈Finset.range N,f ((j:ℝ)/M))-(∫ x in 0..((N:ℝ)/M),f x)|≤((N:ℝ)/M)*ε := by
  have hle (j : ℕ) : (j:ℝ)/M≤((j:ℝ)+1)/M := (div_le_div_iff_of_pos_right hM).mpr (by linarith)
  have hi (j : ℕ) (hj : j<N) : IntervalIntegrable f volume ((j:ℝ)/M) (((j:ℝ)+1)/M) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (hle j)]
    apply hf.mono
    intro x hx
    have hjR : (j:ℝ)+1≤N := by exact_mod_cast (show j+1≤N by omega)
    exact ⟨le_trans (by positivity) hx.1,le_trans hx.2 ((div_le_div_iff_of_pos_right hM).mpr hjR)⟩
  have he (j : ℕ) (hj : j<N) :
      |(1/M)*f ((j:ℝ)/M)-(∫ x in (j:ℝ)/M..((j:ℝ)+1)/M,f x)|≤ε/M := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=(j:ℝ)/M) (b:=((j:ℝ)+1)/M) (C:=ε) (f:=fun x => f ((j:ℝ)/M)-f x)
      (fun x hx => by
        rw [uIoc_of_le (hle j)] at hx
        simpa only [Real.norm_eq_abs] using hmod j hj x ⟨hx.1.le,hx.2⟩)
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hi j hj),intervalIntegral.integral_const,
      Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hle j))] at h
    have hd : ((j:ℝ)+1)/M-(j:ℝ)/M=1/M := by ring
    rw [hd] at h
    simpa only [smul_eq_mul,div_eq_mul_inv,mul_one,one_mul] using h
  have hsum := Finset.sum_le_sum (s:=Finset.range N) (fun j hj => he j (Finset.mem_range.mp hj))
  have hadd := intervalIntegral.sum_integral_adjacent_intervals (a:=fun j : ℕ => (j:ℝ)/M)
    (n:=N) (fun j hj => by simpa only [Nat.cast_add,Nat.cast_one] using hi j hj)
  simp only [Nat.cast_zero,zero_div] at hadd
  have htriangle := Finset.abs_sum_le_sum_abs (s:=Finset.range N)
    (f:=fun j : ℕ => (1/M)*f ((j:ℝ)/M)-(∫ x in (j:ℝ)/M..((j:ℝ)+1)/M,f x))
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at htriangle
  have hadd' : (∑ j∈Finset.range N,∫ x in (j:ℝ)/M..((j:ℝ)+1)/M,f x)=∫ x in 0..(N:ℝ)/M,f x := by
    simpa only [Nat.cast_add,Nat.cast_one] using hadd
  rw [hadd'] at htriangle
  have h := htriangle.trans hsum
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_div_assoc,div_mul_eq_mul_div] using h

theorem grid_sum_integral_endpoint_error (f : ℝ→ℝ) (C M B ε : ℝ) (hC : 0≤C) (hM : 0<M)
    (N : ℕ) (hN : (N:ℝ)/M≤C) (hgap : C-(N:ℝ)/M≤1/M)
    (hf : ContinuousOn f (Icc 0 C)) (hB : ∀ x ∈ Icc 0 C,|f x|≤B)
    (hmod : ∀ j : ℕ,j<N → ∀ x ∈ Icc ((j:ℝ)/M) (((j:ℝ)+1)/M),|f ((j:ℝ)/M)-f x|≤ε)
    (hε : 0≤ε) :
    |(1/M)*(∑ j∈Finset.range (N+1),f ((j:ℝ)/M))-(∫ x in 0..C,f x)|≤C*ε+2*B/M := by
  have hN0 : 0≤(N:ℝ)/M := by positivity
  have hB0 : 0≤B := le_trans (abs_nonneg _) (hB 0 ⟨le_rfl,hC⟩)
  have hfirst := uniform_grid_integral_error f M hM N ε (hf.mono (Icc_subset_Icc le_rfl hN)) hmod
  have htail : |∫ x in (N:ℝ)/M..C,f x|≤B/M := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=(N:ℝ)/M) (b:=C) (C:=B) (f:=f) (fun x hx => by
        rw [uIoc_of_le hN] at hx
        simpa only [Real.norm_eq_abs] using hB x ⟨hN0.trans hx.1.le,hx.2⟩)
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hN)] at h
    exact h.trans (by simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hgap hB0)
  have hlast : |(1/M)*f ((N:ℝ)/M)|≤B/M := by
    rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤1/M)]
    have h := mul_le_mul_of_nonneg_left (hB ((N:ℝ)/M) ⟨hN0,hN⟩) (show 0≤1/M by positivity)
    simpa [div_eq_mul_inv,mul_comm] using h
  have hi1 : IntervalIntegrable f volume 0 ((N:ℝ)/M) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hN0]
    exact hf.mono (Icc_subset_Icc le_rfl hN)
  have hi2 : IntervalIntegrable f volume ((N:ℝ)/M) C := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hN]
    exact hf.mono (Icc_subset_Icc hN0 le_rfl)
  rw [Finset.sum_range_succ,← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have he : (1/M)*((∑ j∈Finset.range N,f ((j:ℝ)/M))+f ((N:ℝ)/M))-
      ((∫ x in 0..(N:ℝ)/M,f x)+(∫ x in (N:ℝ)/M..C,f x))=
      ((1/M)*(∑ j∈Finset.range N,f ((j:ℝ)/M))-(∫ x in 0..(N:ℝ)/M,f x))+
      (1/M)*f ((N:ℝ)/M)-(∫ x in (N:ℝ)/M..C,f x) := by ring
  rw [he]
  calc
    _ ≤ |(1/M)*(∑ j∈Finset.range N,f ((j:ℝ)/M))-(∫ x in 0..(N:ℝ)/M,f x)|+
        |(1/M)*f ((N:ℝ)/M)|+|∫ x in (N:ℝ)/M..C,f x| := (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ C*ε+2*B/M := by rw [mul_div_assoc]; linarith [mul_le_mul_of_nonneg_right hN hε]
end OddZeta.FourValue

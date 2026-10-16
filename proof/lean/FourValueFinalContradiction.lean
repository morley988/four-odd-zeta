import FourValueGlobalArithmeticLower
import FourValueNumericalBridge
import Mathlib.NumberTheory.Real.Irrational

/-! Final comparison. All numerical hypotheses are explicit in this module.
The supplied-certificate wrapper is in FourValueFinal. -/
noncomputable section
namespace OddZeta.FourValue
open Filter
open scoped Topology

theorem final_rate_gap :
    (-288/25:ℝ)-(-577853339/50000000)=1853339/50000000 := by norm_num

/-- The two proved rates are incompatible under simultaneous rationality. -/
theorem not_all_rational_of_certificates
    (G : ArithmeticCertificate.Grid) (hG : G.Valid)
    (hfinite : Numerical.FiniteKnotCertificate) :
    ¬ ∃ z : Fin 4 → ℚ,
      ∀ i, riemannZeta ((![7,9,11,13] : Fin 4 → ℂ) i)=(z i:ℂ) := by
  rintro ⟨z,hz⟩
  obtain ⟨E,hE,hupper⟩ := Numerical.numerical_rate_of_finite_certificate hfinite
  have hsmall := hE.eventually (eventually_lt_nhds (show (0:ℝ)<1 by norm_num))
  have hlower := ArithmeticCertificate.global_arithmetic_lower_of_certificate G hG z hz
  obtain ⟨n,hn,hs,rows,cols,q,hq,he,hl⟩ :=
    (eventually_ge_atTop (1:ℕ) |>.and (hsmall.and hlower)).exists
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hsq : (0:ℝ)<(n:ℝ)^2 := sq_pos_of_pos hnR
  have herror : E n < (n:ℝ)^2 := by simpa using (div_lt_iff₀ hsq).mp hs
  have hu : ‖((analyticZetaMatrix n).submatrix rows cols).det‖ ≤
      Real.exp ((100*(n:ℝ))^2*(-577853339/50000000)+E n) :=
    hupper n hn rows cols
  rw [he] at hu
  have hnorm : ‖(q:ℂ)‖=|(q:ℝ)| := by
    rw [show (q:ℂ)=((q:ℝ):ℂ) by simp,Complex.norm_real,Real.norm_eq_abs]
  rw [hnorm] at hu
  have hpos : 0 < |(q:ℝ)| := abs_pos.mpr (by exact_mod_cast hq)
  have hlog := (Real.log_le_iff_le_exp hpos).mpr hu
  nlinarith

/-- Real zeta at integer arguments, expressed by its ordinary convergent series. -/
def realZeta (k : ℕ) : ℝ := ∑' n : ℕ, 1/(n:ℝ)^k

theorem realZeta_cast (k : ℕ) (hk : 1<k) :
    (realZeta k:ℂ)=riemannZeta (k:ℂ) := by
  rw [realZeta,Complex.ofReal_tsum,zeta_nat_eq_tsum_of_gt_one hk]
  congr 1
  funext n
  simp

theorem realZeta_eq_re (k : ℕ) (hk : 1<k) :
    realZeta k=(riemannZeta (k:ℂ)).re := by
  have h := congrArg Complex.re (realZeta_cast k hk)
  simpa using h

/-- At least one of the four real zeta values is irrational. -/
theorem irrational_one_of_four_of_certificates
    (G : ArithmeticCertificate.Grid) (hG : G.Valid)
    (hfinite : Numerical.FiniteKnotCertificate) :
    Irrational (realZeta 7) ∨ Irrational (realZeta 9) ∨
    Irrational (realZeta 11) ∨ Irrational (realZeta 13) := by
  classical
  by_contra h
  push Not at h
  have hr (i : Fin 4) : ∃ q : ℚ, (q:ℝ)=realZeta ((![7,9,11,13]:Fin 4 → ℕ) i) := by
    fin_cases i
    · simpa [Irrational] using h.1
    · simpa [Irrational] using h.2.1
    · simpa [Irrational] using h.2.2.1
    · simpa [Irrational] using h.2.2.2
  choose z hz using hr
  apply not_all_rational_of_certificates G hG hfinite
  refine ⟨z,?_⟩
  intro i
  have hk : 1<((![7,9,11,13]:Fin 4 → ℕ) i) := by fin_cases i <;> norm_num
  have hc := realZeta_cast ((![7,9,11,13]:Fin 4 → ℕ) i) hk
  have hi : (((![7,9,11,13]:Fin 4 → ℕ) i):ℂ)=((![7,9,11,13]:Fin 4 → ℂ) i) := by
    fin_cases i <;> norm_num
  rw [hi,← hz i] at hc
  simpa using hc.symm

end OddZeta.FourValue

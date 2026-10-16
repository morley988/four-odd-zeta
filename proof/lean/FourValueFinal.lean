import FourValueFinalContradiction
import FourValueFullGrid
import FourValueExternalGlobalArithmetic

/-! Final supplied-certificate theorem.
This module introduces no admissions. Its conclusions depend on the eight
explicitly marked finite numerical admissions in the three external modules.
Use the corresponding `_of_certificates` theorems to expose the hypotheses. -/
noncomputable section
namespace OddZeta.FourValue

theorem not_all_four_zeta_rational :
    ¬ ∃ z : Fin 4 → ℚ,
      ∀ i, riemannZeta ((![7,9,11,13] : Fin 4 → ℂ) i)=(z i:ℂ) := by
  obtain ⟨G,hG⟩ := ArithmeticCertificate.external_grid_certificate
  exact not_all_rational_of_certificates G hG FullGrid.finite_knots

/-- At least one of ζ(7), ζ(9), ζ(11), ζ(13) is irrational,
conditional on the eight isolated external finite-calculation admissions. -/
theorem irrational_one_of_four :
    Irrational (realZeta 7) ∨ Irrational (realZeta 9) ∨
    Irrational (realZeta 11) ∨ Irrational (realZeta 13) := by
  obtain ⟨G,hG⟩ := ArithmeticCertificate.external_grid_certificate
  exact irrational_one_of_four_of_certificates G hG FullGrid.finite_knots

/-- The same conclusion directly in terms of Mathlib's Riemann zeta function. -/
theorem irrational_zeta7_or_zeta9_or_zeta11_or_zeta13 :
    Irrational (riemannZeta 7).re ∨ Irrational (riemannZeta 9).re ∨
    Irrational (riemannZeta 11).re ∨ Irrational (riemannZeta 13).re := by
  simpa only [realZeta_eq_re 7 (by norm_num), realZeta_eq_re 9 (by norm_num),
    realZeta_eq_re 11 (by norm_num), realZeta_eq_re 13 (by norm_num),
    Nat.cast_ofNat] using irrational_one_of_four

end OddZeta.FourValue

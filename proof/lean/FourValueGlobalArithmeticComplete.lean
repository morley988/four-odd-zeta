import FourValueGlobalArithmeticLower
import FourValueExternalGlobalArithmetic

noncomputable section
namespace OddZeta.FourValue.ArithmeticCertificate
open Filter Corrected

theorem global_arithmetic_lower
 (z : Fin 4 → ℚ)
 (hz : ∀i,riemannZeta ((![7,9,11,13]:Fin 4 → ℂ) i)=(z i:ℂ)) :
 ∀ᶠ n : ℕ in atTop,
 ∃ (rows cols : Fin (analyticMinorSize n) ↪ Fin (targetHankelDegree n+1)) (q : ℚ),
 q≠0 ∧ ((analyticZetaMatrix n).submatrix rows cols).det=(q:ℂ) ∧
 (100*(n:ℝ))^2*(-288/25)≤Real.log |(q:ℝ)| := by
 obtain ⟨G,hG⟩ := external_grid_certificate
 exact global_arithmetic_lower_of_certificate G hG z hz

#print axioms external_grid_certificate
#print axioms global_arithmetic_lower
end OddZeta.FourValue.ArithmeticCertificate

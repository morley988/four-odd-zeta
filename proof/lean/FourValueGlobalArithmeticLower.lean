import FourValueGlobalArithmeticRate

noncomputable section
namespace OddZeta.FourValue.ArithmeticCertificate
open Filter Corrected

theorem global_arithmetic_lower_of_certificate (G : Grid) (hG : G.Valid)
 (z : Fin 4 → ℚ)
 (hz : ∀i,riemannZeta ((![7,9,11,13]:Fin 4 → ℂ) i)=(z i:ℂ)) :
 ∀ᶠ n : ℕ in atTop,
 ∃ (rows cols : Fin (analyticMinorSize n) ↪ Fin (targetHankelDegree n+1)) (q : ℚ),
 q≠0 ∧ ((analyticZetaMatrix n).submatrix rows cols).det=(q:ℂ) ∧
 (100*(n:ℝ))^2*(-288/25)≤Real.log |(q:ℝ)| := by
 let z' : Fin 4 → ℚ := fun i => (![15,70,210,495]:Fin 4 → ℚ) i*z i
 filter_upwards [G.eventual_log_lower hG z',eventually_ge_atTop (1:ℕ)] with n hn hn1
 obtain ⟨rows,cols,hne⟩ := analyticZetaMatrix_nonzero_minor n hn1
 have he := analyticZetaMatrix_selected_rational n z hz rows cols
 let q := ((Corrected.rationalFourValueMatrix n z').submatrix rows cols).det
 have hq : q≠0 := by
   intro hh
   apply hne
   rw [he]
   change (q:ℂ)=0
   simp [hh]
 exact ⟨rows,cols,q,hq,he,hn rows cols hq⟩

#print axioms global_arithmetic_lower_of_certificate
end OddZeta.FourValue.ArithmeticCertificate

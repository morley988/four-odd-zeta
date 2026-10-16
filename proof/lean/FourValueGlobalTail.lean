import FourValueGlobalCosts

noncomputable section
namespace OddZeta.FourValue.Corrected
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem centeredResidueCount_one_large (a : ℤ) (b : ℕ)
 (ha : a∈poleWindow b) (hb : 2*b<p) : centeredResidueCount p a b=1 := by
 rw [centeredResidueCount_floor]
 simp only [poleWindow,mem_Icc] at ha
 have h1 : (b:ℤ)+a<(p:ℤ) := by omega
 have h2 : (b:ℤ)-a<(p:ℤ) := by omega
 rw [Int.ediv_eq_zero_of_lt (by omega) h1,Int.ediv_eq_zero_of_lt (by omega) h2]
 norm_num

theorem targetNormalizationFloor_zero_large (n : ℕ) (hp : 126*n<p) :
 targetNormalizationFloor p n=0 := by
 unfold targetNormalizationFloor
 have h1 (i : Fin 10) : 2*targetFactorialEndpoints i*n<p := by
   have := targetFactorialEndpoints_le i
   nlinarith
 simp only [Nat.div_eq_of_lt (by omega : 33*n<p),Nat.cast_zero,mul_zero,sub_zero]
 apply sum_eq_zero
 intro i hi
 rw [Nat.div_eq_of_lt (h1 i)]
 rfl

theorem integralLocalMatrix_integral_large (n : ℕ) (lambda : Fin 4 → ℚ)
 (r : Fin (p/2+1)) {k d : ℕ} (rows cols : Fin k → Fin d)
 (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda) (hl : 130*n<p) :
 PadicLower p 0
   ((integralLocalMatrix n (67*n) (pairedPoles n r) lambda d).submatrix rows cols).det := by
 have h := integralLocalMatrix_single n (67*n) (pairedPoles n r) r.val lambda rows cols hs hp
   (fun a ha => ⟨(mem_pairedPoles n r a ha).1,
     centeredResidueCount_one_large a (63*n) (mem_pairedPoles n r a ha).1 (by omega),
     (mem_pairedPoles n r a ha).2,by
       have haw := (mem_pairedPoles n r a ha).1
       simp only [poleWindow,mem_Icc] at haw
       omega⟩)
 apply h.mono
 rw [targetNormalizationFloor_zero_large n (by omega),mul_zero]
 exact le_max_right _ _

theorem selectedFactorialCost_zero_large (n : ℕ) {k : ℕ}
 (rows cols : Fin k → Fin (targetHankelDegree n+1)) (hl : 361*n<p) :
 selectedFactorialCost p n rows cols=0 := by
 have hv (i : Fin (targetHankelDegree n+1)) : padicValNat p (2*i.val).factorial=0 := by
   apply padicValNat.eq_zero_of_not_dvd
   rw [(Fact.out : p.Prime).dvd_factorial]
   have hi := i.isLt
   unfold targetHankelDegree at hi
   omega
 simp [selectedFactorialCost,hv]

/-- No missing negative valuation tail remains above the largest factorial index. -/
theorem rationalFourValueMatrix_integral_large (n : ℕ) (lambda : Fin 4 → ℚ) {k : ℕ}
 (rows cols : Fin k → Fin (targetHankelDegree n+1))
 (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda) (hl : 361*n<p) :
 PadicLower p 0 ((rationalFourValueMatrix n lambda).submatrix rows cols).det := by
 have h := rationalFourValueMatrix_dual_bound n lambda rows cols 0 (fun _ => 0)
   (fun r m u v => by
     simpa using integralLocalMatrix_integral_large n lambda r u v hs hp (by omega))
 simpa [selectedFactorialCost_zero_large n rows cols hl] using h

#print axioms rationalFourValueMatrix_integral_large
#print axioms integralLocalMatrix_integral_large
end OddZeta.FourValue.Corrected

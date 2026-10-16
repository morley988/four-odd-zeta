import FourValueUniformLaurent

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem centeredResidueCount_one_unique (b : ℕ) (a t : ℤ)
    (ha : a∈poleWindow b) (ht : t∈poleWindow b)
    (hc : centeredResidueCount p a b=1) (hd : (p:ℤ)∣a-t) : a=t := by
  rw [centeredResidueCount_eq_card] at hc
  have hc' : ((poleWindow b).filter (fun z => (p:ℤ)∣a-z)).card=1 := by exact_mod_cast hc
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp hc'
  have ha' : a∈(poleWindow b).filter (fun z => (p:ℤ)∣a-z) := by simp [ha]
  have ht' : t∈(poleWindow b).filter (fun z => (p:ℤ)∣a-z) := by
    simp only [Finset.mem_filter]
    exact ⟨ht,hd⟩
  rw [hz,Finset.mem_singleton] at ha' ht'
  exact ha'.trans ht'.symm

theorem singleNode_root_condition (n : ℕ) (a : ℤ) (ha : a∈poleWindow (63*n))
    (hc : centeredResidueCount p a (63*n)=1) :
    ∀ t∈targetPoleList n,a=t ∨ ¬(p:ℤ)∣a-t := by
  intro t ht
  by_cases hd : (p:ℤ)∣a-t
  · exact Or.inl (centeredResidueCount_one_unique _ a t ha (targetPoleList_bound n t ht) hc hd)
  · exact Or.inr hd

theorem localFourValueObservation_uniform_good (b : ℕ) (a : ℤ) (lambda : Fin 4 → ℚ)
    (f : RatFunc ℚ) (w : ℤ) (hm : (b-a).toNat<p)
    (hl : ∀ i,PadicLower p 0 (lambda i))
    (hf : ∀ k<10,PadicLower p w (rationalCoefficientAt (a:ℚ) (-((k+1:ℕ):ℤ)) f)) :
    PadicLower p w (localFourValueObservation b a lambda f) := by
  have hC : PadicLower p w (localFourthObservation b a f) := by
    apply PadicLower.neg
    apply padicLower_sum
    intro k hk
    have h := (fourthHarmonicBracket_padicLower_good (b-a).toNat k hm).mul
      (hf k (Finset.mem_range.mp hk))
    simpa [mul_assoc] using h
  have h (i : Fin 4) (k : ℕ) (hk : k<10) :
      PadicLower p w (lambda i*rationalCoefficientAt (a:ℚ) (-((k+1:ℕ):ℤ)) f) := by
    simpa using (hl i).mul (hf k hk)
  exact ((((hC.add (h 0 2 (by decide))).add (h 1 4 (by decide))).add
    (h 2 6 (by decide))).add (h 3 8 (by decide)))

theorem singleNode_local_good (n b : ℕ) (a : ℤ) (lambda : Fin 4 → ℚ)
    (P : ℚ[X]) (w : ℤ) (hP : PolynomialPadicLower p w P)
    (ha : a∈poleWindow (63*n)) (hc : centeredResidueCount p a (63*n)=1)
    (hm : (b-a).toNat<p) (hp : ¬p∣rationalPencilDenominator lambda) :
    PadicLower p (targetNormalizationValuation p n+w)
      (localFourValueObservation b a lambda (rationalPhysicalTest n P)) := by
  apply localFourValueObservation_uniform_good _ _ _ _ _ hm
    (rationalPencil_integral_at_prime lambda hp)
  intro k hk
  exact rationalPhysicalTest_uniformLaurent n a P w hP
    (singleNode_root_condition n a ha hc) _

theorem translatedPhysicalMonomial_integral (r : ℤ) (m : ℕ) :
    PolynomialPadicLower p 0 (translatedPhysicalMonomial r m) := by
  have h := (integerLinearFactor_polynomialPadicLower (p:=p) (4*r^2)).pow m
  simpa [translatedPhysicalMonomial] using h

theorem singleNode_residueMatrix_det (n b : ℕ) (S : Finset ℤ) (r : ℤ)
    (lambda : Fin 4 → ℚ) {k : ℕ} (rows cols : Fin k → ℕ)
    (hp : ¬p∣rationalPencilDenominator lambda)
    (hS : ∀ a∈S,a∈poleWindow (63*n) ∧ centeredResidueCount p a (63*n)=1 ∧ (b-a).toNat<p) :
    PadicLower p ((k:ℤ)*targetNormalizationValuation p n)
      (residueClassMatrix n b S r lambda rows cols).det := by
  have h := padicLower_det_weighted (p:=p) (residueClassMatrix n b S r lambda rows cols)
    (fun _ => 0) (fun _ => 0) (targetNormalizationValuation p n) (fun i j => by
      apply padicLower_sum
      intro a ha
      obtain ⟨haw,hac,hab⟩ := hS a ha
      simpa using singleNode_local_good n b a lambda _ 0
        (translatedPhysicalMonomial_integral r (rows i+cols j)) haw hac hab hp)
  simpa using h

theorem PadicLower.max {u v : ℤ} {q : ℚ} (hu : PadicLower p u q) (hv : PadicLower p v q) :
    PadicLower p (max u v) q := by
  rcases hu with hz | hu
  · exact Or.inl hz
  rcases hv with hz | hv
  · exact Or.inl hz
  exact Or.inr (max_le hu hv)

theorem singleNode_residueMatrix_det_max (n b : ℕ) (S : Finset ℤ) (r : ℤ)
    (lambda : Fin 4 → ℚ) {k : ℕ} (rows cols : Fin k → ℕ)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hs : 800*n<p^2) (hp : ¬p∣rationalPencilDenominator lambda)
    (hS : ∀ a∈S,a∈poleWindow (63*n) ∧ centeredResidueCount p a (63*n)=1 ∧
      ((p:ℤ)∣a-r ∨ (p:ℤ)∣a+r) ∧ (b-a).toNat<p) :
    PadicLower p (max ((k:ℤ)^2+targetLocalWeight p n r*k)
      ((k:ℤ)*targetNormalizationFloor p n))
      (residueClassMatrix n b S r lambda rows cols).det := by
  apply PadicLower.max
  · apply pairedResidueClassMatrix_det_padicLower_good n b S r lambda rows cols hr hc hs hp
    intro a ha
    obtain ⟨haw,hac,har,hab⟩ := hS a ha
    refine ⟨?_,har,hab⟩
    simp only [poleWindow,Finset.mem_Icc] at haw ⊢
    omega
  · have h := singleNode_residueMatrix_det n b S r lambda rows cols hp
      (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1,(hS a ha).2.2.2⟩)
    rw [← targetNormalization_padicVal, targetNormalization_padicVal_large n hs] at h
    exact h
end OddZeta.FourValue

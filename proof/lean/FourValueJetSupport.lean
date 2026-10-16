import FourValueFiniteJets
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic

/-! Finite-support jet algebra used by the Pearson classification. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K]

/-- A multiplier nonzero at the origin acts injectively on bounded jets. -/
theorem jetMultiply_unit_kernel (d : ℕ) (U : K[X] →ₗ[K] K)
    (hU : JetBound U d) (b : K[X]) (hb : b.coeff 0 ≠ 0)
    (hzero : jetMultiply b U = 0) : U = 0 := by
  have htop : U (X^d) = 0 := by
    have h := LinearMap.congr_fun hzero (X^d)
    change U (b * X^d) = 0 at h
    rw [jetBound_top_multiply U d hU b] at h
    exact (mul_eq_zero.mp h).resolve_left hb
  induction d generalizing U with
  | zero =>
      apply linearFunctional_zero_of_powers
      intro j
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact htop
      · exact hU j hj
  | succ d ih =>
      have hsmall : JetBound U d := by
        intro j hj
        by_cases h : j = d+1
        · simpa [h] using htop
        · exact hU j (by omega)
      have htop' : U (X^d) = 0 := by
        have h := LinearMap.congr_fun hzero (X^d)
        change U (b * X^d) = 0 at h
        rw [jetBound_top_multiply U d hsmall b] at h
        exact (mul_eq_zero.mp h).resolve_left hb
      exact ih U hsmall hzero htop'

/-- Translate a center jet to the point `a`. -/
def jetAt (a : K) (U : K[X] →ₗ[K] K) : K[X] →ₗ[K] K :=
  U.comp (Polynomial.taylor a)

@[simp] theorem jetAt_apply (a : K) (U : K[X] →ₗ[K] K) (f : K[X]) :
    jetAt a U f = U (Polynomial.taylor a f) := rfl

theorem jetAt_zero_iff (a : K) (U : K[X] →ₗ[K] K) : jetAt a U = 0 ↔ U=0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro f
    have h' := LinearMap.congr_fun h (Polynomial.taylor (-a) f)
    simpa [jetAt, Polynomial.taylor_taylor] using h'
  · rintro rfl
    simp [jetAt]

theorem jetAt_multiply (a : K) (U : K[X] →ₗ[K] K) (q : K[X]) :
    jetMultiply q (jetAt a U) = jetAt a (jetMultiply (Polynomial.taylor a q) U) := by
  apply LinearMap.ext
  intro f
  simp [jetMultiply_apply]

/-- A jet of order at most `d` at `a` annihilates every multiple of
`(X-a)^(d+1)`. -/
theorem jetAt_annihilates (a : K) (U : K[X] →ₗ[K] K) (d : ℕ)
    (hU : JetBound U d) (f : K[X]) :
    jetAt a U ((X-C a)^(d+1)*f) = 0 := by
  simp only [jetAt_apply, Polynomial.taylor_mul, Polynomial.taylor_pow,
    map_sub, Polynomial.taylor_X, Polynomial.taylor_C, add_sub_cancel_right]
  rw [mul_comm]
  exact jetBound_vanishes_multiple U d hU (Polynomial.taylor a f) (d+1) (by omega)

theorem jetAt_vanishes_divisible (a : K) (U : K[X] →ₗ[K] K) (d : ℕ)
    (hU : JetBound U d) (f : K[X]) (hdiv : (X-C a)^(d+1) ∣ f) :
    jetAt a U f = 0 := by
  obtain ⟨g, rfl⟩ := hdiv
  exact jetAt_annihilates a U d hU g

/-- A finite sum of jets at distinct points has a unique decomposition. -/
theorem finite_jets_sum_zero (s : Finset K) (U : K → K[X] →ₗ[K] K) (d : K → ℕ)
    (hU : ∀ a ∈ s, JetBound (U a) (d a))
    (hsum : ∑ a ∈ s, jetAt a (U a) = 0) : ∀ a ∈ s, U a = 0 := by
  classical
  intro a ha
  let q : K[X] := ∏ b ∈ s.erase a, (X-C b)^(d b+1)
  have hq (b : K) (hb : b ∈ s) (hne : b ≠ a) : (X-C b)^(d b+1) ∣ q := by
    exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hne, hb⟩)
  have hpoint : jetMultiply q (jetAt a (U a)) = 0 := by
    apply LinearMap.ext
    intro f
    have h := LinearMap.congr_fun hsum (q*f)
    simp only [LinearMap.sum_apply, LinearMap.zero_apply] at h
    rw [Finset.sum_eq_single a] at h
    · exact h
    · intro b hb hne
      exact jetAt_vanishes_divisible b (U b) (d b) (hU b hb) (q*f)
        (dvd_mul_of_dvd_left (hq b hb hne) f)
    · exact fun hnot => False.elim (hnot ha)
  rw [jetAt_multiply, jetAt_zero_iff] at hpoint
  have hconstant : (Polynomial.taylor a q).coeff 0 ≠ 0 := by
    rw [Polynomial.taylor_coeff_zero]
    simp only [q, Polynomial.eval_prod, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hb).1))
  exact jetMultiply_unit_kernel (d a) (U a) (hU a ha) _ hconstant hpoint

end OddZeta.FourValue

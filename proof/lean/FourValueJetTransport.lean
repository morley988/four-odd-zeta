import FourValueJetDecomposition
import Mathlib.Tactic

/-! Invertible local transport and the cumulative order budget for jets. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K]

 theorem jetMultiply_mul (a b : K[X]) (U : K[X] →ₗ[K] K) :
    jetMultiply a (jetMultiply b U) = jetMultiply (a*b) U := by
  apply LinearMap.ext
  intro f
  simp only [jetMultiply_apply]
  congr 1
  ring

theorem jetMultiply_comm (a b : K[X]) (U : K[X] →ₗ[K] K) :
    jetMultiply a (jetMultiply b U) = jetMultiply b (jetMultiply a U) := by
  rw [jetMultiply_mul, jetMultiply_mul, mul_comm]

theorem jetBound_multiply (U : K[X] →ₗ[K] K) (d : ℕ)
    (hU : JetBound U d) (a : K[X]) : JetBound (jetMultiply a U) d := by
  intro k hk
  exact jetBound_vanishes_multiple U d hU a k hk

theorem jetBound_sub (U V : K[X] →ₗ[K] K) (d : ℕ)
    (hU : JetBound U d) (hV : JetBound V d) : JetBound (U-V) d := by
  intro k hk
  simp [hU k hk, hV k hk]

theorem jetMultiply_unit_injective (d : ℕ) (U V : K[X] →ₗ[K] K)
    (hU : JetBound U d) (hV : JetBound V d) (b : K[X]) (hb : b.coeff 0 ≠ 0)
    (heq : jetMultiply b U = jetMultiply b V) : U=V := by
  apply sub_eq_zero.mp
  apply jetMultiply_unit_kernel d (U-V) (jetBound_sub U V d hU hV) b hb
  apply LinearMap.ext
  intro f
  have h := LinearMap.congr_fun heq f
  simpa [jetMultiply_apply, sub_eq_zero] using h

/-- A nonzero constant coefficient gives a polynomial Bezout identity with
any power of `X`, hence an inverse on each bounded jet space. -/
theorem polynomial_coprime_X_of_constant (b : K[X]) (hb : b.coeff 0 ≠ 0) :
    IsCoprime b X := by
  refine ⟨C ((b.coeff 0)⁻¹), -C ((b.coeff 0)⁻¹)*b.divX, ?_⟩
  calc
    _ = C ((b.coeff 0)⁻¹)*(X*b.divX+C (b.coeff 0)) +
        (-C ((b.coeff 0)⁻¹)*b.divX)*X := by rw [b.X_mul_divX_add]
    _ = C ((b.coeff 0)⁻¹)*C (b.coeff 0) := by ring
    _ = 1 := by rw [← C_mul]; simp [hb]

/-- Multiplication by a polynomial nonzero at the point is a bijection on
bounded jets, with the inverse constructed algebraically. -/
theorem jetMultiply_unit_exists_unique (d : ℕ) (U : K[X] →ₗ[K] K)
    (hU : JetBound U d) (b : K[X]) (hb : b.coeff 0 ≠ 0) :
    ∃! V : K[X] →ₗ[K] K, JetBound V d ∧ jetMultiply b V = U := by
  obtain ⟨r,s,hrs⟩ := (polynomial_coprime_X_of_constant b hb).pow_right (n:=d+1)
  refine ⟨jetMultiply r U, ⟨jetBound_multiply U d hU r, ?_⟩, ?_⟩
  · apply LinearMap.ext
    intro f
    simp only [jetMultiply_apply]
    have hz : U ((s*f)*X^(d+1))=0 :=
      jetBound_vanishes_multiple U d hU (s*f) (d+1) (by omega)
    have heq : r*(b*f)+(s*f)*X^(d+1)=f := by
      calc
        _ = (r*b+s*X^(d+1))*f := by ring
        _ = f := by rw [hrs, one_mul]
    have h := congrArg U heq
    rw [map_add, hz, add_zero] at h
    exact h
  · intro V hV
    exact jetMultiply_unit_injective d V (jetMultiply r U) hV.1
      (jetBound_multiply U d hU r) b hb (by
        rw [hV.2]
        apply LinearMap.ext
        intro f
        simp only [jetMultiply_apply]
        have hz : U ((s*f)*X^(d+1))=0 :=
          jetBound_vanishes_multiple U d hU (s*f) (d+1) (by omega)
        have heq : r*(b*f)+(s*f)*X^(d+1)=f := by
          calc
            _ = (r*b+s*X^(d+1))*f := by ring
            _ = f := by rw [hrs, one_mul]
        have h := congrArg U heq
        rw [map_add, hz, add_zero] at h
        exact h.symm)

/-- Every local Pearson step with unit denominator has one and only one
successor in a prescribed bounded jet space. -/
theorem jet_transport_exists_unique (d : ℕ) (U : K[X] →ₗ[K] K)
    (hU : JetBound U d) (a b : K[X]) (hb : b.coeff 0 ≠ 0) :
    ∃! V : K[X] →ₗ[K] K,
      JetBound V d ∧ jetMultiply b V = jetMultiply a U :=
  jetMultiply_unit_exists_unique d (jetMultiply a U) (jetBound_multiply U d hU a) b hb

/-- Multiplying the consecutive local equations telescopes the transport
along a finite chain. No invertibility is needed for this identity. -/
theorem jet_transport_chain (V : ℕ → K[X] →ₗ[K] K) (a b : ℕ → K[X]) (N : ℕ)
    (hstep : ∀ j < N, jetMultiply (a j) (V j) = jetMultiply (b j) (V (j+1))) :
    jetMultiply (∏ j ∈ Finset.range N, a j) (V 0) =
      jetMultiply (∏ j ∈ Finset.range N, b j) (V N) := by
  induction N with
  | zero => simp [jetMultiply]
  | succ N ih =>
      have hi := ih (fun j hj => hstep j (by omega))
      rw [Finset.prod_range_succ, Finset.prod_range_succ,
        ← jetMultiply_mul, jetMultiply_comm, hi, jetMultiply_comm,
        hstep N (by omega), jetMultiply_comm, jetMultiply_mul, mul_comm]

/-- If a terminal zero forces a multiplier `X^t*u` to kill the center jet,
with `u(0) != 0`, the center jet has order strictly below `t`. -/
theorem jet_annihilator_order_bound (U : K[X] →ₗ[K] K) (d t : ℕ)
    (hU : JetBound U d) (u : K[X]) (hu : u.coeff 0 ≠ 0)
    (hkill : jetMultiply (X^t*u) U = 0) :
    ∀ k : ℕ, t ≤ k → U (X^k)=0 := by
  have hz : jetMultiply (X^t) U = 0 := by
    apply jetMultiply_unit_kernel d _ (jetBound_multiply U d hU (X^t)) u hu
    rw [jetMultiply_mul, mul_comm]
    exact hkill
  intro k hk
  have h := LinearMap.congr_fun hz (X^(k-t))
  simpa [jetMultiply_apply, ← pow_add, Nat.add_sub_of_le hk] using h

/-- Fifteen crossed roots give the precise center-jet cutoff used by the
four-value argument. The multiplier factorization remains explicit. -/
theorem jet_fifteen_roots_center_bound (U : K[X] →ₗ[K] K) (d : ℕ)
    (hU : JetBound U d) (u : K[X]) (hu : u.coeff 0 ≠ 0)
    (hkill : jetMultiply (X^15*u) U = 0) : JetBound U 14 := by
  intro k hk
  exact jet_annihilator_order_bound U d 15 hU u hu hkill k (by omega)

end OddZeta.FourValue

import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

/-! The odd lift from the squared coordinate `Y` to the physical coordinate
`z`. It preserves finite annihilators by replacing `p(Y)` with `p(z²)`. -/

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K]

/-- Extract coefficients of odd powers, and divide their exponents by two:
`sum a_j z^j` is sent to `sum a_(2j+1) Y^j`. -/
def oddCompress : K[X] →ₗ[K] K[X] where
  toFun f := Polynomial.contract 2 f.divX
  map_add' f g := by
    ext j
    simp [Polynomial.coeff_contract, Polynomial.coeff_divX]
  map_smul' a f := by
    ext j
    simp [Polynomial.coeff_contract, Polynomial.coeff_divX]

@[simp] theorem oddCompress_coeff (f : K[X]) (j : ℕ) :
    (oddCompress f).coeff j = f.coeff (2 * j + 1) := by
  simp [oddCompress, Polynomial.coeff_contract, Polynomial.coeff_divX, mul_comm]

theorem oddCompress_expand (p : K[X]) : oddCompress (expand K 2 p) = 0 := by
  ext j
  rw [oddCompress_coeff, Polynomial.coeff_expand (by decide)]
  have h : ¬ 2 ∣ 2 * j + 1 := by omega
  simp [h]

theorem divX_X_mul (p : K[X]) : (X * p).divX = p := by
  ext j
  simp [Polynomial.coeff_divX]

theorem divX_mul_formula (f g : K[X]) :
    (f * g).divX = f.divX * g + C (f.coeff 0) * g.divX := by
  conv_lhs => rw [← f.X_mul_divX_add]
  rw [add_mul, Polynomial.divX_add]
  simp [mul_assoc, divX_X_mul, Polynomial.divX_C_mul]

theorem contract_two_smul (a : K) (f : K[X]) :
    contract 2 (a • f) = a • contract 2 f := by
  ext j
  simp [Polynomial.coeff_contract]

/-- Squared-coordinate multiplication commutes with the odd extraction. -/
theorem oddCompress_mul_expand (f p : K[X]) :
    oddCompress (f * expand K 2 p) = oddCompress f * p := by
  change contract 2 (f * expand K 2 p).divX = contract 2 f.divX * p
  rw [divX_mul_formula, Polynomial.contract_add (by decide),
    Polynomial.contract_mul_expand (by decide)]
  have hz : contract 2 (C (f.coeff 0) * (expand K 2 p).divX) = 0 := by
    rw [← Polynomial.smul_eq_C_mul, contract_two_smul]
    change f.coeff 0 • oddCompress (expand K 2 p) = 0
    rw [oddCompress_expand, smul_zero]
  rw [hz, add_zero]

/-- The lift recovers the original polynomial on odd squared-coordinate
test functions. -/
theorem oddCompress_X_expand (p : K[X]) :
    oddCompress (X * expand K 2 p) = p := by
  change contract 2 (X * expand K 2 p).divX = p
  rw [divX_X_mul]
  exact Polynomial.contract_expand (R := K) (p := 2) (by decide)

def oddLift (L : K[X] →ₗ[K] K) : K[X] →ₗ[K] K := L.comp oddCompress

@[simp] theorem oddLift_apply (L : K[X] →ₗ[K] K) (f : K[X]) :
    oddLift L f = L (oddCompress f) := rfl

theorem oddLift_X_expand (L : K[X] →ₗ[K] K) (p : K[X]) :
    oddLift L (X * expand K 2 p) = L p := by
  simp [oddCompress_X_expand]

/-- The lift is annihilated by `p(z²)` whenever the original functional is
annihilated by `p(Y)`. This is the finite-dimensional quotient bridge. -/
theorem oddLift_annihilator (L : K[X] →ₗ[K] K) (p : K[X])
    (hp : ∀ q : K[X], L (p * q) = 0) (f : K[X]) :
    oddLift L (expand K 2 p * f) = 0 := by
  rw [oddLift_apply, mul_comm, oddCompress_mul_expand, mul_comm]
  exact hp _

/-- The lifted functional is odd under reflection of the physical variable. -/
theorem oddCompress_reflect (f : K[X]) :
    oddCompress (f.comp (-X)) = -oddCompress f := by
  ext j
  rw [oddCompress_coeff]
  have hx : (-X : K[X]) = C (-1) * X := by simp
  rw [hx, Polynomial.comp_C_mul_X_coeff]
  simp [oddCompress_coeff, pow_add, pow_mul]

theorem oddLift_reflect (L : K[X] →ₗ[K] K) (f : K[X]) :
    oddLift L (f.comp (-X)) = -oddLift L f := by
  simp [oddCompress_reflect]

/-- An odd coefficient cannot exceed the degree of the original polynomial. -/
theorem oddCompress_degree_bound (f : K[X]) (d : ℕ)
    (h : f.natDegree ≤ 2 * d + 2) : (oddCompress f).natDegree ≤ d := by
  by_cases hz : oddCompress f = 0
  · simp [hz]
  · have hc : (oddCompress f).coeff (oddCompress f).natDegree ≠ 0 := by
      simpa only [Polynomial.coeff_natDegree] using
        (Polynomial.leadingCoeff_ne_zero.mpr hz)
    rw [oddCompress_coeff] at hc
    have hd := Polynomial.le_natDegree_of_ne_zero hc
    omega

end OddZeta.FourValue

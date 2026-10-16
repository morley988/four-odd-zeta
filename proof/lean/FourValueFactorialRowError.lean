import FourValueUniformStirling

noncomputable section
namespace OddZeta.FourValue

def factorialRowRate (s : ℝ) : ℝ := -4*s*Real.log (2*s)+4*s

theorem log_factorial_main_lower (m : ℕ) : (m:ℝ)*Real.log (m:ℝ)-(m:ℝ)≤Real.log (Nat.factorial m:ℝ) := by
  by_cases hm : m=0
  · simp [hm]
  have h := (log_factorial_explicit_bounds m (by omega)).1
  have hl : 0≤Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤m by omega))
  nlinarith

theorem factorial_row_scaled_identity (i : ℕ) (M : ℝ) (hM : 0<M) :
    4*(i:ℝ)*Real.log M-2*((2*(i:ℝ))*Real.log (2*(i:ℝ))-2*(i:ℝ))=
      M*factorialRowRate ((i:ℝ)/M) := by
  by_cases hi : i=0
  · simp [hi,factorialRowRate]
  have hi0 : (0:ℝ)< i := by exact_mod_cast (show 0< i by omega)
  have he : 2*((i:ℝ)/M)=(2*(i:ℝ))/M := by ring
  unfold factorialRowRate
  rw [he,Real.log_div (by positivity) hM.ne']
  field_simp
  <;> ring

theorem factorial_row_uniform_error (i : ℕ) (M : ℝ) (hM : 0<M) :
    |(4*(i:ℝ)*Real.log M-2*Real.log (Nat.factorial (2*i):ℝ))-
      M*factorialRowRate ((i:ℝ)/M)|≤Real.log (2*(i:ℝ)+1)+2 := by
  have h := log_factorial_main_error (2*i)
  have he := factorial_row_scaled_identity i M hM
  push_cast at h
  apply abs_le.mpr
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor <;> linarith

theorem factorial_row_main_upper (i : ℕ) (M : ℝ) (hM : 0<M) :
    4*(i:ℝ)*Real.log M-2*Real.log (Nat.factorial (2*i):ℝ)≤
      M*factorialRowRate ((i:ℝ)/M) := by
  have h := log_factorial_main_lower (2*i)
  have he := factorial_row_scaled_identity i M hM
  push_cast at h
  linarith
end OddZeta.FourValue

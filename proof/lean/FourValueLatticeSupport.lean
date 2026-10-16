import FourValueSupportChains
import Mathlib.Tactic

/-! Exact root geometry of the four-value Pearson polynomial and the
resulting even-lattice support restriction. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem linearRootProduct_eval_zero_iff (roots : List K) (x : K) :
    (linearRootProduct roots).eval x=0 ↔ x ∈ roots := by
  induction roots with
  | nil => simp [linearRootProduct]
  | cons a roots ih =>
      change ((X-C a)*linearRootProduct roots).eval x=0 ↔ x ∈ a::roots
      simp [ih, sub_eq_zero]

theorem pearsonPolynomial_eval_zero_iff (n x : K) :
    (pearsonPolynomial n).eval x=0 ↔
      x=-(200*n+2) ∨ x ∈ physicalEndpointRoots n := by
  rw [pearsonPolynomial, Polynomial.eval_mul, mul_eq_zero,
    linearRootProduct_eval_zero_iff]
  simp [add_eq_zero_iff_eq_neg]

def halfEndpointRoots (n : ℤ) : List ℤ :=
  [67*n,67*n,67*n,67*n,67*n,63*n,60*n,58*n,57*n,
    54*n,52*n,49*n,47*n,44*n,42*n]

theorem physicalEndpointRoots_half (n : ℤ) :
    physicalEndpointRoots (n:K) = (halfEndpointRoots n).map (fun (t : ℤ) => 2*(t:K)) := by
  simp only [physicalEndpointRoots, halfEndpointRoots, List.map_cons, List.map_nil]
  push_cast
  congr 1 <;> ring

theorem halfEndpointRoots_bounds (n t : ℤ) (hn : 0≤n)
    (ht : t ∈ halfEndpointRoots n) : 0≤t ∧ t≤67*n := by
  simp only [halfEndpointRoots, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> omega

/-- Every root is an even integer: one negative exceptional root, or a
nonnegative endpoint of size at most `134*n`. -/
theorem pearson_root_integer (n : ℕ) (x : K)
    (hx : (pearsonPolynomial (n:K)).eval x=0) :
    ∃ t : ℤ, x=2*(t:K) ∧
      (t= -100*(n:ℤ)-1 ∨ (0≤t ∧ t≤67*(n:ℤ))) := by
  rw [pearsonPolynomial_eval_zero_iff] at hx
  rcases hx with hx | hx
  · refine ⟨-100*(n:ℤ)-1, ?_, Or.inl rfl⟩
    rw [hx]
    push_cast
    ring
  · have hmap := physicalEndpointRoots_half (K:=K) (n:ℤ)
    simp only [Int.cast_natCast] at hmap
    rw [hmap] at hx
    obtain ⟨t,ht,hxt⟩ := List.mem_map.mp hx
    exact ⟨t,hxt.symm,Or.inr (halfEndpointRoots_bounds _ _ (by omega) ht)⟩

/-- The sum condition from a finite chain rules out the exceptional
negative root at either endpoint. -/
theorem admissible_root_pair_nonnegative (n k l : ℕ) (t u : ℤ)
    (ht : t= -100*(n:ℤ)-1 ∨ (0≤t ∧ t≤67*(n:ℤ)))
    (hu : u= -100*(n:ℤ)-1 ∨ (0≤u ∧ u≤67*(n:ℤ)))
    (hsum : t+u=(k:ℤ)+l) :
    0≤t ∧ t≤67*(n:ℤ) ∧ 0≤u ∧ u≤67*(n:ℤ) := by
  rcases ht with ht | ht <;> rcases hu with hu | hu <;> omega

/-- The actual support bound, with no assumption that support was on a
lattice to begin with. Every nonzero jet lies at an even integer between
`-134*n` and `134*n`. -/
theorem finitePearson_even_lattice_support (n : ℕ) (J : JetFamily K) (d : ℕ)
    (hJ : JetsBound J d)
    (hU : IsFinitePearson (pearsonPolynomial (n:K)) (realizeJets J))
    (a : K) (ha : J a≠0) :
    ∃ v : ℤ, a=2*(v:K) ∧ -67*(n:ℤ)≤v ∧ v≤67*(n:ℤ) := by
  obtain ⟨k,hk,_⟩ := finitePearson_forward_endpoint _ J d hJ hU a ha
  obtain ⟨l,hl,_⟩ := finitePearson_backward_endpoint _ J d hJ hU a ha
  obtain ⟨t,ht,htr⟩ := pearson_root_integer n _ hk
  obtain ⟨u,hu,hur⟩ := pearson_root_integer n _ hl
  have hsumK : (t:K)+(u:K)=(k:K)+(l:K) := by linear_combination -(ht+hu)/2
  have hsum : t+u=(k:ℤ)+l := by exact_mod_cast hsumK
  obtain ⟨ht0,htb,hu0,hub⟩ := admissible_root_pair_nonnegative n k l t u htr hur hsum
  refine ⟨t-(k:ℤ), ?_, ?_, ?_⟩
  · push_cast
    linear_combination ht
  · omega
  · omega

end OddZeta.FourValue

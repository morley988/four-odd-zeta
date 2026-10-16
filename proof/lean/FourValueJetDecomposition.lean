import FourValueJetSupport
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-! Existence of finite jet decompositions, by explicit Bezout splitting. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K]

def Annihilates (L : K[X] →ₗ[K] K) (p : K[X]) : Prop :=
  ∀ f : K[X], L (p*f)=0

/-- Coprime factors split an annihilated functional into its two primary
components. The construction uses a Bezout identity. -/
theorem annihilator_coprime_split (L : K[X] →ₗ[K] K) (a b : K[X])
    (hab : IsCoprime a b) (hL : Annihilates L (a*b)) :
    ∃ L₁ L₂ : K[X] →ₗ[K] K,
      L = L₁+L₂ ∧ Annihilates L₁ a ∧ Annihilates L₂ b := by
  obtain ⟨r,s,hrs⟩ := hab
  refine ⟨jetMultiply (s*b) L, jetMultiply (r*a) L, ?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro f
    simp only [LinearMap.add_apply, jetMultiply_apply]
    rw [← map_add, ← add_mul, add_comm (s*b) (r*a), hrs, one_mul]
  · intro f
    change L (s*b*(a*f))=0
    rw [show s*b*(a*f)=(a*b)*(s*f) by ring]
    exact hL (s*f)
  · intro f
    change L (r*a*(b*f))=0
    rw [show r*a*(b*f)=(a*b)*(r*f) by ring]
    exact hL (r*f)

/-- Split over any finite family of pairwise coprime annihilator factors. -/
theorem annihilator_product_decomposition {ι : Type*} (s : Finset ι)
    (p : ι → K[X])
    (hcop : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → IsCoprime (p a) (p b))
    (L : K[X] →ₗ[K] K) (hL : Annihilates L (∏ a ∈ s, p a)) :
    ∃ V : ι → K[X] →ₗ[K] K,
      L = ∑ a ∈ s, V a ∧ ∀ a ∈ s, Annihilates (V a) (p a) := by
  classical
  induction s using Finset.induction_on generalizing L with
  | empty =>
      refine ⟨fun _ => 0, ?_, by simp⟩
      simp only [Finset.sum_empty]
      apply LinearMap.ext
      intro f
      simpa [Annihilates] using hL f
  | @insert a s ha ih =>
      have hcop' : IsCoprime (p a) (∏ b ∈ s, p b) := by
        apply IsCoprime.prod_right
        intro b hb
        exact hcop a (by simp) b (by simp [hb]) (by aesop)
      have hL' : Annihilates L (p a * ∏ b ∈ s, p b) := by
        simpa [Finset.prod_insert ha] using hL
      obtain ⟨L₁,L₂,hadd,h₁,h₂⟩ := annihilator_coprime_split L _ _ hcop' hL'
      obtain ⟨V,hV,hann⟩ := ih (fun b hb c hc hbc =>
        hcop b (by simp [hb]) c (by simp [hc]) hbc) L₂ h₂
      refine ⟨Function.update V a L₁, ?_, ?_⟩
      · rw [Finset.sum_insert ha]
        simp only [Function.update_self]
        rw [hadd, hV]
        congr 1
        apply Finset.sum_congr rfl
        intro b hb
        simp [Function.update_of_ne (show b ≠ a by aesop)]
      · intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · simpa using h₁
        · simpa [Function.update_of_ne (show b ≠ a by aesop)] using hann b hb

/-- Annihilation by a root power gives a bounded jet after translation. -/
theorem annihilator_root_power_jet (a : K) (n : ℕ) (L : K[X] →ₗ[K] K)
    (hL : Annihilates L ((X-C a)^n)) :
    JetBound (jetAt (-a) L) n ∧ L = jetAt a (jetAt (-a) L) := by
  constructor
  · intro j hj
    simp only [jetAt_apply, Polynomial.taylor_X_pow, map_neg, ← sub_eq_add_neg]
    have hn : n ≤ j := by omega
    have heq : (X-C a)^j = (X-C a)^n * (X-C a)^(j-n) := by
      rw [← pow_add, Nat.add_sub_of_le hn]
    rw [heq]
    exact hL _
  · apply LinearMap.ext
    intro f
    simp [Polynomial.taylor_taylor]

/-- Every functional annihilated by a product of root powers has a finite
jet representation. Multiplicities may vary and need not be one. -/
theorem root_product_jet_decomposition (s : Finset K) (n : K → ℕ)
    (L : K[X] →ₗ[K] K)
    (hL : Annihilates L (∏ a ∈ s, (X-C a)^(n a))) :
    ∃ V : K → K[X] →ₗ[K] K,
      L = ∑ a ∈ s, jetAt a (V a) ∧ ∀ a ∈ s, JetBound (V a) (n a) := by
  have hcop : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      IsCoprime ((X-C a)^(n a)) ((X-C b)^(n b)) := by
    intro a _ b _ hab
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hab).isUnit).pow
  obtain ⟨W,hW,hann⟩ := annihilator_product_decomposition s _ hcop L hL
  refine ⟨fun a => jetAt (-a) (W a), ?_, ?_⟩
  · rw [hW]
    apply Finset.sum_congr rfl
    intro a ha
    exact (annihilator_root_power_jet a (n a) (W a) (hann a ha)).2
  · intro a ha
    exact (annihilator_root_power_jet a (n a) (W a) (hann a ha)).1

/-- A split nonzero polynomial annihilator gives an actual finite jet
representation. Together with `finite_jets_sum_zero`, this proves the
existence and uniqueness of local components. -/
theorem finite_functional_jet_decomposition (p : K[X]) (hp : p ≠ 0)
    (hsplit : p.Splits) (L : K[X] →ₗ[K] K) (hL : Annihilates L p) :
    ∃ (s : Finset K) (d : K → ℕ) (V : K → K[X] →ₗ[K] K),
      L = ∑ a ∈ s, jetAt a (V a) ∧ ∀ a ∈ s, JetBound (V a) (d a) := by
  classical
  have hprod : Annihilates L (∏ a ∈ p.roots.toFinset,
      (X-C a)^(p.rootMultiplicity a)) := by
    intro f
    have h := hL f
    conv_lhs at h => rw [hsplit.eq_prod_roots, Polynomial.prod_multiset_root_eq_finset_root]
    rw [mul_assoc, ← Polynomial.smul_eq_C_mul, map_smul] at h
    exact (smul_eq_zero.mp h).resolve_left (Polynomial.leadingCoeff_ne_zero.mpr hp)
  obtain ⟨V,hV,hbound⟩ := root_product_jet_decomposition p.roots.toFinset
    (fun a => p.rootMultiplicity a) L hprod
  exact ⟨p.roots.toFinset, (fun a => p.rootMultiplicity a), V, hV, hbound⟩

end OddZeta.FourValue

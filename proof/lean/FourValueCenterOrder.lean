import FourValueCenterControl
import Mathlib.Tactic

/-! The exact fifteen-root budget in the positive transport chain. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]
local instance : DecidableEq K := Classical.decEq K

theorem linearRootProduct_roots (r : List K) :
    (linearRootProduct r).roots = (r : Multiset K) := by
  change ((r : Multiset K).map (fun a => X-C a)).prod.roots = _
  exact Polynomial.roots_multiset_prod_X_sub_C _

theorem linearRootProduct_rootMultiplicity (r : List K) (x : K) :
    (linearRootProduct r).rootMultiplicity x = r.count x := by
  classical
  rw [← Polynomial.count_roots, linearRootProduct_roots]
  simp

/-- Counting a list's roots along an injective finite grid counts every
occurrence, so repeated endpoint roots retain their multiplicity. -/
theorem sum_list_counts_on_grid {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → K) (hf : Function.Injective f) (r : List K)
    (hr : ∀ x ∈ r, ∃ i ∈ s, f i=x) :
    ∑ i ∈ s, r.count (f i) = r.length := by
  classical
  induction r with
  | nil => simp
  | cons x r ih =>
      obtain ⟨j,hj,hfj⟩ := hr x (by simp)
      have hr' : ∀ y ∈ r, ∃ i ∈ s, f i=y := fun y hy => hr y (by simp [hy])
      have hcount : (∑ i ∈ s, if x=f i then 1 else 0 : ℕ)=1 := by
        rw [Finset.sum_eq_single j]
        · simp [hfj]
        · intro i hi hij
          have hne : x≠f i := by
            intro h
            apply hij
            exact hf (h.symm.trans hfj.symm)
          simp [hne]
        · exact fun hnot => False.elim (hnot hj)
      simp only [List.count_cons, beq_iff_eq, List.length_cons]
      rw [Finset.sum_add_distrib, ih hr']
      omega

theorem physicalEndpointRoots_in_positive_grid (n : ℕ) (x : K)
    (hx : x ∈ physicalEndpointRoots (n:K)) :
    ∃ j ∈ Finset.range (67*n+1), (2:K)*j=x := by
  classical
  have hmap := physicalEndpointRoots_half (K:=K) (n:ℤ)
  simp only [Int.cast_natCast] at hmap
  rw [hmap] at hx
  obtain ⟨t,ht,hxt⟩ := List.mem_map.mp hx
  obtain ⟨ht0,htb⟩ := halfEndpointRoots_bounds _ _ (by omega) ht
  refine ⟨t.toNat, Finset.mem_range.mpr (by omega), ?_⟩
  have hc : (t.toNat:K)=(t:K) := by exact_mod_cast Int.toNat_of_nonneg ht0
  rw [hc]
  exact hxt

theorem pearson_rootMultiplicity_nonnegative (n j : ℕ) :
    (pearsonPolynomial (n:K)).rootMultiplicity (2*(j:K)) =
      (physicalEndpointRoots (n:K)).count (2*(j:K)) := by
  classical
  rw [pearsonPolynomial, Polynomial.rootMultiplicity_mul
    ((pearsonPolynomial_monic (n:K)).ne_zero)]
  have hnon : ¬IsRoot ((X+C (200*(n:K)+2))^5) (2*(j:K)) := by
    change ((X+C (200*(n:K)+2))^5).eval (2*(j:K)) ≠ 0
    simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    apply pow_ne_zero
    have hnat : 2*j+200*n+2≠0 := by omega
    have hc : ((2*j+200*n+2:ℕ):K)≠0 := by exact_mod_cast hnat
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_assoc] using hc
  rw [Polynomial.rootMultiplicity_eq_zero hnon, zero_add,
    linearRootProduct_rootMultiplicity]

/-- Sum of the exact multiplicities along the positive lattice is fifteen. -/
theorem pearson_positive_root_budget (n : ℕ) :
    (∑ j ∈ Finset.range (67*n+1),
      (pearsonPolynomial (n:K)).rootMultiplicity (2*(j:K))) = 15 := by
  classical
  simp_rw [pearson_rootMultiplicity_nonnegative]
  have hi : Function.Injective (fun j : ℕ => (2:K)*j) := by
    intro j k h
    exact Nat.cast_injective (mul_left_cancel₀ (by norm_num : (2:K)≠0) h)
  have h := sum_list_counts_on_grid (K:=K) (Finset.range (67*n+1)) _ hi
    (physicalEndpointRoots (n:K)) (physicalEndpointRoots_in_positive_grid n)
  simpa [physicalEndpointRoots] using h

theorem rootMultiplicity_finset_prod {ι : Type*} (s : Finset ι) (p : ι → K[X])
    (hp : ∀ i ∈ s, p i≠0) (x : K) :
    (∏ i ∈ s, p i).rootMultiplicity x = ∑ i ∈ s, (p i).rootMultiplicity x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hprod : ∏ j ∈ s, p j ≠ 0 := Finset.prod_ne_zero_iff.mpr
        (fun j hj => hp j (by simp [hj]))
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        Polynomial.rootMultiplicity_mul (mul_ne_zero (hp i (by simp)) hprod),
        ih (fun j hj => hp j (by simp [hj]))]

def positiveTransportProduct (n : ℕ) : K[X] :=
  ∏ j ∈ Finset.range (67*n+1), Polynomial.taylor (2*(j:K)) (pearsonPolynomial (n:K))

theorem positiveTransportProduct_ne_zero (n : ℕ) :
    positiveTransportProduct (K:=K) n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact (Polynomial.taylor_eq_zero _ _).not.mpr (pearsonPolynomial_monic (n:K)).ne_zero

/-- The accumulated numerator has exactly a fifteenfold center zero. -/
theorem positiveTransportProduct_order (n : ℕ) :
    (positiveTransportProduct (K:=K) n).rootMultiplicity 0 = 15 := by
  rw [positiveTransportProduct, rootMultiplicity_finset_prod]
  · have ht (j : ℕ) :
        (Polynomial.taylor (2*(j:K)) (pearsonPolynomial (n:K))).rootMultiplicity 0 =
          (pearsonPolynomial (n:K)).rootMultiplicity (2*(j:K)) := by
      simpa [Polynomial.taylor_apply] using Polynomial.rootMultiplicity_comp_C_mul_X_add_C
        (pearsonPolynomial (n:K)) 1 (2*(j:K)) 0 isUnit_one
    simp_rw [ht]
    exact pearson_positive_root_budget n
  · intro j _
    exact (Polynomial.taylor_eq_zero _ _).not.mpr (pearsonPolynomial_monic (n:K)).ne_zero

/-- An explicit unit factor exists after removing the fifteen center roots. -/
theorem positiveTransportProduct_factor (n : ℕ) :
    ∃ u : K[X], u.coeff 0≠0 ∧ positiveTransportProduct n=X^15*u := by
  obtain ⟨u,hu,hndiv⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd
    (positiveTransportProduct (K:=K) n) (positiveTransportProduct_ne_zero n) 0
  simp only [Polynomial.C_0, sub_zero, positiveTransportProduct_order] at hu hndiv
  exact ⟨u, fun h => hndiv (Polynomial.X_dvd_iff.mpr h), hu⟩

/-- The actual finite Pearson center jet has order at most fourteen.
This discharges the numerical multiplicity premise for the exact family. -/
theorem finitePearson_center_order_bound (n : ℕ) (J : JetFamily K) (d : ℕ)
    (hJ : JetsBound J d)
    (hU : IsFinitePearson (pearsonPolynomial (n:K)) (realizeJets J)) :
    JetBound (J 0) 14 := by
  have hend : J (2*((67*n+1:ℕ):K))=0 := by
    by_contra hz
    obtain ⟨v,hv,_,hvb⟩ := finitePearson_even_lattice_support n J d hJ hU _ hz
    have heqK : ((67*n+1:ℕ):K)=(v:K) :=
      mul_left_cancel₀ (by norm_num : (2:K)≠0) hv
    have heq : (67*(n:ℤ)+1)=v := by exact_mod_cast heqK
    omega
  have hstep : ∀ j<67*n+1,
      jetMultiply (Polynomial.taylor (2*(j:K)) (pearsonPolynomial (n:K))) (J (2*j)) =
      jetMultiply (Polynomial.taylor (2*((j+1:ℕ):K))
        ((pearsonPolynomial (n:K)).comp (-X))) (J (2*((j+1:ℕ):K))) := by
    intro j _
    have h := finitePearson_local_transport (pearsonPolynomial (n:K)) J d hJ hU (2*j)
    simpa [Nat.cast_add, Nat.cast_one, mul_add] using h
  have hchain := jet_transport_chain (fun j => J (2*(j:K)))
    (fun j => Polynomial.taylor (2*(j:K)) (pearsonPolynomial (n:K)))
    (fun j => Polynomial.taylor (2*((j+1:ℕ):K)) ((pearsonPolynomial (n:K)).comp (-X)))
    (67*n+1) hstep
  have hkill : jetMultiply (positiveTransportProduct n) (J 0)=0 := by
    apply LinearMap.ext
    intro f
    have h := LinearMap.congr_fun hchain f
    simpa only [positiveTransportProduct, Nat.cast_zero, mul_zero, hend,
      jetMultiply_apply, LinearMap.zero_apply] using h
  obtain ⟨u,hu,hfactor⟩ := positiveTransportProduct_factor (K:=K) n
  rw [hfactor] at hkill
  exact jet_fifteen_roots_center_bound (J 0) d (hJ 0) u hu hkill

end OddZeta.FourValue

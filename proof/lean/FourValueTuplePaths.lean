import FourValueTuplePearson
import Mathlib.Tactic

/-! All admissible endpoint tuples are connected to the all-b tuple by
single-coordinate increases, with the degree parameter never decreasing. -/
noncomputable section
namespace OddZeta.FourValue
open scoped BigOperators

def tupleDeficit (b : ℕ) (a : Fin 15 → ℕ) : ℕ := ∑ i : Fin 15, (b-a i)

def seedTuple (b : ℕ) : Fin 15 → ℕ := fun i => if i.val<6 then b else 0

theorem tuple_sum_update {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (a : Fin 15 → ℕ) (i : Fin 15) (v : ℕ) :
    (∑ j,f (Function.update a i v j))=f v+∑ j ∈ Finset.univ.erase i,f (a j) := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1]

theorem tupleBeta_update_succ (b : ℕ) (a : Fin 15 → ℕ) (i : Fin 15) :
    tupleBeta b (Function.update a i (a i+1))=tupleBeta b a+1 := by
  rw [tupleBeta,tuple_sum_update,tupleBeta,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  push_cast
  ring

theorem tupleDeficit_update_succ (b : ℕ) (a : Fin 15 → ℕ) (i : Fin 15) (hi : a i<b) :
    tupleDeficit b (Function.update a i (a i+1))<tupleDeficit b a := by
  rw [tupleDeficit,tuple_sum_update,tupleDeficit,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  omega

theorem tuple_update_succ_bounded (b : ℕ) (a : Fin 15 → ℕ) (ha : ∀ i,a i≤b)
    (i : Fin 15) (hi : a i<b) : ∀ j,Function.update a i (a i+1) j≤b := by
  intro j
  by_cases hji : j=i
  · subst j
    simp only [Function.update_self]
    omega
  · simpa [hji] using ha j

theorem seedTuple_bounded (b : ℕ) : ∀ i,seedTuple b i≤b := by
  intro i
  simp only [seedTuple]
  split_ifs <;> omega

theorem seedTuple_beta (b : ℕ) : tupleBeta b (seedTuple b)=b := by
  norm_num [tupleBeta,seedTuple,Fin.sum_univ_succ]
  ring

/-- Any property invariant under admissible elementary endpoint changes
has the same value at every admissible tuple as at the all-b tuple. -/
theorem admissible_tuple_property_iff_all (b : ℕ) (P : (Fin 15 → ℕ) → Prop)
    (hstep : ∀ a, (∀ i,a i≤b) → 6≤tupleBeta b a →
      ∀ i,a i<b → (P (Function.update a i (a i+1)) ↔ P a)) :
    ∀ a, (∀ i,a i≤b) → 6≤tupleBeta b a → (P a ↔ P (fun _ => b)) := by
  intro a
  generalize hd : tupleDeficit b a=d
  induction d using Nat.strong_induction_on generalizing a with
  | h d ih =>
      intro ha hbeta
      by_cases hall : a=(fun _ => b)
      · rw [hall]
      · have hex : ∃ i,a i<b := by
          by_contra h
          push_neg at h
          apply hall
          funext i
          exact le_antisymm (ha i) (h i)
        obtain ⟨i,hi⟩ := hex
        let a' := Function.update a i (a i+1)
        have hsmall : tupleDeficit b a'<d := by
          rw [← hd]
          exact tupleDeficit_update_succ b a i hi
        have hnew : P a' ↔ P (fun _ => b) := ih _ hsmall a' rfl
          (tuple_update_succ_bounded b a ha i hi)
          (by change 6≤tupleBeta b (Function.update a i (a i+1));
              rw [tupleBeta_update_succ]; omega)
        exact (hstep a ha hbeta i hi).symm.trans hnew

/-- A proof at the six-b/nine-zero seed propagates to every admissible tuple. -/
theorem admissible_tuple_property_of_seed (b : ℕ) (hb : 6≤b)
    (P : (Fin 15 → ℕ) → Prop)
    (hstep : ∀ a, (∀ i,a i≤b) → 6≤tupleBeta b a →
      ∀ i,a i<b → (P (Function.update a i (a i+1)) ↔ P a))
    (hseed : P (seedTuple b)) (a : Fin 15 → ℕ)
    (ha : ∀ i,a i≤b) (hbeta : 6≤tupleBeta b a) : P a := by
  have hcommon := (admissible_tuple_property_iff_all b P hstep (seedTuple b)
    (seedTuple_bounded b) (by rw [seedTuple_beta]; exact_mod_cast hb)).mp hseed
  exact (admissible_tuple_property_iff_all b P hstep a ha hbeta).mpr hcommon

end OddZeta.FourValue

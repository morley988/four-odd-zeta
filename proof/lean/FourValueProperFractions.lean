import FourValueLaurentAtoms
import FourValueIntervalProducts
import Mathlib.FieldTheory.RatFunc.Degree

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def IsProperRational (f : RatFunc K) : Prop := f=0 ∨ f.intDegree<0

theorem IsProperRational.zero : IsProperRational (0:RatFunc K) := Or.inl rfl

theorem IsProperRational.add {f g : RatFunc K} (hf : IsProperRational f)
    (hg : IsProperRational g) : IsProperRational (f+g) := by
  rcases hf with rfl | hf
  · simpa using hg
  rcases hg with rfl | hg
  · simpa [IsProperRational] using (Or.inr hf : f=0 ∨ f.intDegree<0)
  by_cases hz : f+g=0
  · exact Or.inl hz
  · exact Or.inr ((RatFunc.intDegree_add_le (by intro h; simpa [h] using hg) hz).trans_lt
      (max_lt hf hg))

theorem IsProperRational.neg {f : RatFunc K} (hf : IsProperRational f) :
    IsProperRational (-f) := by
  rcases hf with rfl | hf
  · exact Or.inl neg_zero
  · exact Or.inr (by simpa using hf)

theorem IsProperRational.sub {f g : RatFunc K} (hf : IsProperRational f)
    (hg : IsProperRational g) : IsProperRational (f-g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem IsProperRational.smul (c : K) {f : RatFunc K} (hf : IsProperRational f) :
    IsProperRational (c • f) := by
  by_cases hc : c=0
  · simp [hc,IsProperRational]
  rcases hf with rfl | hf
  · simp [IsProperRational]
  · right
    rw [RatFunc.smul_eq_C_mul,RatFunc.intDegree_mul
      (by simpa using RatFunc.C_injective.ne hc) (by intro h; simpa [h] using hf),RatFunc.intDegree_C,zero_add]
    exact hf

theorem IsProperRational.sum {ι : Type*} (S : Finset ι) (f : ι → RatFunc K)
    (hf : ∀ i ∈ S,IsProperRational (f i)) : IsProperRational (∑ i ∈ S,f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (IsProperRational.zero (K:=K))
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem isProperRational_fraction (p q : K[X]) (hq : q≠0) (hd : p.natDegree<q.natDegree) :
    IsProperRational (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) := by
  by_cases hp : p=0
  · simp [hp,IsProperRational]
  · right
    rw [RatFunc.intDegree_div (RatFunc.algebraMap_ne_zero hp) (RatFunc.algebraMap_ne_zero hq),
      RatFunc.intDegree_polynomial,RatFunc.intDegree_polynomial]
    omega

theorem isProperRational_pole (a : K) (k : ℕ) (hk : 0<k) :
    IsProperRational (rationalPole a k) := by
  rw [rationalPole_fraction]
  apply isProperRational_fraction 1 ((X-C a)^k)
    (pow_ne_zero _ (Polynomial.monic_X_sub_C a).ne_zero)
  simpa using hk

theorem isProperRational_polynomial_iff (p : K[X]) :
    IsProperRational (algebraMap K[X] (RatFunc K) p) ↔ p=0 := by
  constructor
  · rintro (h | h)
    · exact RatFunc.algebraMap_injective K (by simpa using h)
    · rw [RatFunc.intDegree_polynomial] at h
      omega
  · rintro rfl
    simp [IsProperRational]

/-- A proper rational function whose denominator is a power of a finite
integer-root product has an actual finite partial-fraction expansion. -/
theorem integer_partialFractions (S : Finset ℤ) (m : ℕ) (p : K[X])
    (hp : p.natDegree < (integerRootProduct (K:=K) S ^ m).natDegree) :
    ∃ c : ℤ → Fin m → K,
      algebraMap K[X] (RatFunc K) p /
        algebraMap K[X] (RatFunc K) (integerRootProduct S ^ m) =
      ∑ j ∈ S, ∑ k : Fin m, c j k • rationalPole (j:K) (k.val+1) := by
  classical
  let g : ℤ → K[X] := fun j => X-C (j:K)
  let gi : ℤ → RatFunc K := fun j => (algebraMap K[X] (RatFunc K) (g j))⁻¹
  have hg : ∀ j ∈ S,(g j).Monic := fun _ _ => Polynomial.monic_X_sub_C _
  have hgg : Set.Pairwise (S:Set ℤ) (fun i j => IsCoprime (g i) (g j)) :=
    fun i _ j _ hij => Polynomial.pairwise_coprime_X_sub_C Int.cast_injective hij
  have hgi : ∀ j ∈ S,gi j * algebraMap K[X] (RatFunc K) (g j)=1 :=
    fun j hj => inv_mul_cancel₀ (RatFunc.algebraMap_ne_zero (hg j hj).ne_zero)
  obtain ⟨q,r,hr,heq⟩ := Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    p hg hgg (fun _ => m) hgi
  have hrC (j : ℤ) (hj : j∈S) (k : Fin m) : r j k=C ((r j k).coeff 0) := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    by_cases hz : r j k=0
    · simp [hz]
    · have h := hr j hj k
      rw [show (g j).degree=1 by exact Polynomial.degree_X_sub_C _] at h
      change (r j k).degree < (1:ℕ) at h
      have hn := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr h
      omega
  let c : ℤ → Fin m → K := fun j k => (r j k).coeff 0
  have heq' : algebraMap K[X] (RatFunc K) p /
      algebraMap K[X] (RatFunc K) (integerRootProduct S ^ m) =
      algebraMap K[X] (RatFunc K) q +
      ∑ j ∈ S,∑ k : Fin m,c j k • rationalPole (j:K) (k.val+1) := by
    convert heq using 1
    · simp [gi,g,integerRootProduct,div_eq_mul_inv,map_prod,Finset.prod_pow,inv_pow]
    · congr 1
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k _
      rw [hrC j hj k,RatFunc.smul_eq_C_mul]
      rfl
  have hf := isProperRational_fraction p (integerRootProduct S ^ m)
    (pow_ne_zero _ (integerRootProduct_monic S).ne_zero) hp
  have hs : IsProperRational (∑ j ∈ S,∑ k : Fin m,c j k • rationalPole (j:K) (k.val+1)) := by
    apply IsProperRational.sum
    intro j hj
    apply IsProperRational.sum
    intro k _
    exact (isProperRational_pole (j:K) (k.val+1) (by omega)).smul (c j k)
  have hq : q=0 := by
    apply (isProperRational_polynomial_iff q).mp
    convert hf.sub hs using 1
    rw [heq',add_sub_cancel_right]
  exact ⟨c,by simpa [hq] using heq'⟩

end OddZeta.FourValue

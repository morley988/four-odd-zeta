import FourValueTuplePearson
import FourValueHankelCoordinates
import Mathlib.Tactic

/-! The companion step on truncated moments uses just one degree-nine
relation. It does not assume that the original functional factors through
the polynomial quotient. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

def shiftedInitialMoments (L : K[X] →ₗ[K] K) (a : K) : Fin 9 → K :=
  fun j => L ((X-C a)*X^j.val)

theorem linear_recurrence_monomials (L : K[X] →ₗ[K] K) (a : K) (d : ℕ)
    (h : ∀ k<d, L ((X-C a)*X^k)=0) :
    ∀ j≤d, L (X^j)=a^j*L 1 := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
      have hr := h j (by omega)
      have heq : ((X-C a)*X^j:K[X])=X^(j+1)-a • X^j := by
        rw [Polynomial.smul_eq_C_mul,pow_succ]
        ring
      rw [heq,map_sub,map_smul,smul_eq_mul] at hr
      rw [sub_eq_zero.mp hr,ih (by omega),pow_succ]
      ring

theorem linear_recurrence_evaluation (L : K[X] →ₗ[K] K) (a : K) (d : ℕ)
    (h : ∀ k<d, L ((X-C a)*X^k)=0) (f : K[X]) (hf : f.natDegree≤d) :
    L f=f.eval a*L 1 := by
  nth_rw 1 [f.as_sum_range_C_mul_X_pow]
  rw [map_sum,Polynomial.eval_eq_sum_range,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul,
    linear_recurrence_monomials L a d h j (by have := Finset.mem_range.mp hj; omega)]
  ring

/-- A nonzero evaluation of the relation excludes an evaluation functional
from the kernel of the truncated endpoint multiplication map. -/
theorem shifted_initial_zero_implies_initial_zero (L : K[X] →ₗ[K] K)
    (p : K[X]) (hp : p.natDegree≤9) (a : K) (hpa : p.eval a≠0)
    (hLp : L p=0) (hshift : shiftedInitialMoments L a=0) : initialMoments L=0 := by
  have hrec : ∀ k<9, L ((X-C a)*X^k)=0 := by
    intro k hk
    exact congrFun hshift ⟨k,hk⟩
  have htop := linear_recurrence_evaluation L a 9 hrec p hp
  have hL1 : L 1=0 := (mul_eq_zero.mp (htop.symm.trans hLp)).resolve_left hpa
  funext j
  change L (X^j.val)=0
  rw [linear_recurrence_monomials L a 9 hrec j.val (by omega),hL1,mul_zero]

theorem functional_relation_forces_top_zero (L : K[X] →ₗ[K] K) (p : K[X]) (d : ℕ)
    (hp : p.natDegree=d) (hlc : p.leadingCoeff≠0) (hLp : L p=0)
    (hinit : ∀ j<d, L (X^j)=0) : L (X^d)=0 := by
  have h := hLp
  rw [p.as_sum_range_C_mul_X_pow,map_sum,hp,Finset.sum_range_succ] at h
  have hlow : (∑ j ∈ Finset.range d, L (C (p.coeff j)*X^j))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [← Polynomial.smul_eq_C_mul,map_smul,hinit j (Finset.mem_range.mp hj),smul_zero]
  rw [hlow,zero_add,← Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul] at h
  have hcoeff : p.coeff d=p.leadingCoeff := hp ▸ Polynomial.coeff_natDegree
  rw [hcoeff] at h
  exact (mul_eq_zero.mp h).resolve_left hlc

theorem initial_zero_implies_shifted_initial_zero (L : K[X] →ₗ[K] K)
    (p : K[X]) (hp : p.natDegree=9) (a : K) (hLp : L p=0)
    (hinit : initialMoments L=0) : shiftedInitialMoments L a=0 := by
  have hz : ∀ j<9, L (X^j)=0 := by
    intro j hj
    exact congrFun hinit ⟨j,hj⟩
  have hlc : p.leadingCoeff≠0 := Polynomial.leadingCoeff_ne_zero.mpr
    (by intro hp0; simp [hp0] at hp)
  have htop := functional_relation_forces_top_zero L p 9 hp hlc hLp hz
  funext j
  change L ((X-C a)*X^j.val)=0
  have hnext : L (X^(j.val+1))=0 := by
    by_cases hj : j.val+1<9
    · exact hz _ hj
    · have heq : j.val+1=9 := by omega
      rwa [heq]
  have heq : ((X-C a)*X^j.val:K[X])=X^(j.val+1)-a • X^j.val := by
    rw [Polynomial.smul_eq_C_mul,pow_succ]
    ring
  rw [heq,map_sub,map_smul,hnext,hz j.val j.isLt,smul_zero,sub_self]

theorem initialMoments_sum {ι : Type*} [Fintype ι] (L : ι → K[X] →ₗ[K] K) (c : ι → K) :
    initialMoments (∑ i,c i • L i)=∑ i,c i • initialMoments (L i) := by
  ext j
  simp [initialMoments]

theorem shiftedInitialMoments_sum {ι : Type*} [Fintype ι]
    (L : ι → K[X] →ₗ[K] K) (c : ι → K) (a : K) :
    shiftedInitialMoments (∑ i,c i • L i) a=∑ i,c i • shiftedInitialMoments (L i) a := by
  ext j
  simp [shiftedInitialMoments]

/-- The actual truncated companion transformation is invertible on the
initial vectors, using only the degree-nine relation and its endpoint value. -/
theorem endpoint_initial_independence_iff {ι : Type*} [Fintype ι]
    (L : ι → K[X] →ₗ[K] K) (p : K[X]) (hp : p.natDegree=9)
    (a : K) (hpa : p.eval a≠0) (hLp : ∀ i,L i p=0) :
    LinearIndependent K (fun i => shiftedInitialMoments (L i) a) ↔
      LinearIndependent K (fun i => initialMoments (L i)) := by
  classical
  simp only [Fintype.linearIndependent_iff]
  constructor
  · intro hi c hc j
    apply hi c ?_ j
    rw [← shiftedInitialMoments_sum]
    apply initial_zero_implies_shifted_initial_zero (∑ i,c i • L i) p hp a
    · simp [hLp]
    · rwa [initialMoments_sum]
  · intro hi c hc j
    apply hi c ?_ j
    rw [← initialMoments_sum]
    apply shifted_initial_zero_implies_initial_zero (∑ i,c i • L i) p hp.le a hpa
    · simp [hLp]
    · rwa [shiftedInitialMoments_sum]

end OddZeta.FourValue

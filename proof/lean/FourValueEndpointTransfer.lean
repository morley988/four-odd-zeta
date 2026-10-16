import FourValueCenterControl
import FourValueFiniteQuotient
import Mathlib.Tactic

/-! The physical difference identity and the invertible endpoint multiplier
in the degree-nine Pearson quotient. -/
noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- Reassemble the odd part exactly in the physical coordinate. -/
theorem oddCompress_reassembly (f : K[X]) :
    (2:K) • (X * expand K 2 (oddCompress f)) = f-f.comp (-X) := by
  ext j
  have href : (f.comp (-X)).coeff j=f.coeff j * (-1:K)^j := by
    rw [show (-X:K[X])=C (-1)*X by simp, Polynomial.comp_C_mul_X_coeff]
  rw [Polynomial.coeff_smul, Polynomial.coeff_sub, href]
  rcases Nat.even_or_odd j with ⟨a,ha⟩ | ⟨a,ha⟩
  · have hj : j=2*a := by omega
    clear ha
    subst j
    cases a with
    | zero => simp
    | succ a =>
        rw [show 2*(a+1)=(2*a+1)+1 by omega, Polynomial.coeff_X_mul,
          Polynomial.coeff_expand (by decide)]
        have hn : ¬2∣2*a+1 := by omega
        simp [hn, pow_add, pow_mul]
  · have hj : j=2*a+1 := by omega
    clear ha
    subst j
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_expand_mul' (by decide), oddCompress_coeff]
    simp [pow_add,pow_mul,smul_eq_mul]
    ring

/-- The coefficient-based Lean operator is precisely the manuscript's
physical difference quotient. -/
theorem pearsonOperator_reassembly (A q : K[X]) :
    X * expand K 2 (pearsonOperator A q) =
      A*q.comp ((X+1)^2)-A.comp (-X)*q.comp ((X-1)^2) := by
  rw [pearsonOperator_apply, map_smul, mul_smul_comm, oddCompress_reassembly,
    Polynomial.mul_comp, Polynomial.comp_assoc]
  congr 2
  simp only [Polynomial.pow_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.one_comp]
  ring

theorem pearsonOperator_eval_identity (A q : K[X]) (a : K) :
    a*(pearsonOperator A q).eval (a^2) =
      A.eval a * q.eval ((a+1)^2) - A.eval (-a)*q.eval ((a-1)^2) := by
  have h := congrArg (Polynomial.eval a) (pearsonOperator_reassembly A q)
  simpa [Polynomial.expand_eq_comp_X_pow, Polynomial.eval_comp, mul_left_comm, mul_assoc] using h

theorem halfEndpointRoots_lower (n t : ℤ) (hn : 0≤n)
    (ht : t ∈ halfEndpointRoots n) : 42*n≤t := by
  simp only [halfEndpointRoots,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- The reflected positive endpoint is never a root of the actual Pearson
polynomial when `n` is positive. -/
theorem pearson_reflected_endpoint_nonzero (n : ℕ) (hn : 0<n) (a : K)
    (ha : a ∈ physicalEndpointRoots (n:K)) :
    (pearsonPolynomial (n:K)).eval (-a)≠0 := by
  have hmap := physicalEndpointRoots_half (K:=K) (n:ℤ)
  simp only [Int.cast_natCast] at hmap
  rw [hmap] at ha
  obtain ⟨t,ht,hat⟩ := List.mem_map.mp ha
  obtain ⟨ht0,htb⟩ := halfEndpointRoots_bounds _ _ (by omega) ht
  have htl := halfEndpointRoots_lower _ _ (by omega) ht
  intro hz
  obtain ⟨u,hu,hur⟩ := pearson_root_integer n (-a) hz
  have heqK : (u:K)=-(t:K) := by linear_combination (hat-hu)/2
  have heq : u = -t := by exact_mod_cast heqK
  rcases hur with hneg | ⟨hu0,hub⟩ <;> omega

/-- The degree-nine relation does not vanish at the squared endpoint,
which is the nonzero determinant condition for the companion step. -/
theorem pearson_relation_endpoint_nonzero (n : ℕ) (hn : 0<n) (a : K)
    (ha : a ∈ physicalEndpointRoots (n:K)) :
    (pearsonOperator (pearsonPolynomial (n:K)) 1).eval (a^2)≠0 := by
  have hroot : (pearsonPolynomial (n:K)).eval a=0 :=
    (pearsonPolynomial_eval_zero_iff _ _).mpr (Or.inr ha)
  have href := pearson_reflected_endpoint_nonzero n hn a ha
  have h := pearsonOperator_eval_identity (pearsonPolynomial (n:K)) 1 a
  simp only [Polynomial.eval_one,hroot,zero_mul,mul_one,zero_sub] at h
  intro hz
  rw [hz,mul_zero] at h
  exact href (neg_eq_zero.mp h.symm)

/-- Nonvanishing evaluation gives a Bezout identity with the corresponding
linear factor. -/
theorem polynomial_coprime_linear_of_eval (p : K[X]) (a : K) (hp : p.eval a≠0) :
    IsCoprime p (X-C a) := by
  have h := polynomial_coprime_X_of_constant (Polynomial.taylor a p)
    (by simpa [Polynomial.taylor_coeff_zero] using hp)
  have hm := h.map (Polynomial.taylorAlgHom (-a)).toRingHom
  simpa [Polynomial.taylor_taylor, sub_eq_add_neg] using hm

/-- The endpoint multiplier is a unit in the actual polynomial quotient. -/
theorem adjoinRoot_linear_isUnit (p : K[X]) (a : K) (hp : p.eval a≠0) :
    IsUnit (AdjoinRoot.mk p (X-C a)) := by
  have h := (polynomial_coprime_linear_of_eval p a hp).map (AdjoinRoot.mk p)
  simpa only [AdjoinRoot.mk_self,isCoprime_zero_left] using h

theorem endpoint_quotient_multiplier_isUnit (n : ℕ) (hn : 0<n) (a : K)
    (ha : a ∈ physicalEndpointRoots (n:K)) :
    IsUnit (AdjoinRoot.mk (pearsonOperator (pearsonPolynomial (n:K)) 1) (X-C (a^2))) :=
  adjoinRoot_linear_isUnit _ _ (pearson_relation_endpoint_nonzero n hn a ha)

/-- Multiplication by an endpoint factor in the Pearson quotient. -/
def quotientEndpointMap (p : K[X]) (a : K) : AdjoinRoot p →ₗ[K] AdjoinRoot p :=
  Algebra.lmul K (AdjoinRoot p) (AdjoinRoot.mk p (X-C a))

theorem quotientEndpointMap_bijective (p : K[X]) (a : K) (hp : p.eval a≠0) :
    Function.Bijective (quotientEndpointMap p a) := by
  exact IsUnit.isUnit_iff_mulLeft_bijective.mp (adjoinRoot_linear_isUnit p a hp)

/-- Precomposition by the quotient endpoint multiplier preserves independence
of any family of quotient functionals. Connecting these functionals to the
manuscript's nine initial moment columns remains a separate task. -/
theorem quotient_endpoint_preserves_independence {ι : Type*} (p : K[X]) (a : K)
    (hp : p.eval a≠0) (v : ι → AdjoinRoot p →ₗ[K] K)
    (hv : LinearIndependent K v) :
    LinearIndependent K (fun i => (v i).comp (quotientEndpointMap p a)) := by
  let T := LinearMap.lcomp K K (quotientEndpointMap p a)
  have hinj : Function.Injective T := by
    intro U V heq
    apply LinearMap.ext
    intro x
    obtain ⟨y,hy⟩ := (quotientEndpointMap_bijective p a hp).surjective x
    have h := LinearMap.congr_fun heq y
    change U (quotientEndpointMap p a y)=V (quotientEndpointMap p a y) at h
    rwa [hy] at h
  exact hv.map_injOn T hinj.injOn

end OddZeta.FourValue

import FourValueUniformLaurent

noncomputable section
namespace OddZeta.FourValue
open Polynomial
open scoped LaurentSeries RatFunc
variable {p : ℕ} [Fact p.Prime]

def ScaledLaurentPadicLower (p : ℕ) (a : ℚ) (s w : ℤ) (f : RatFunc ℚ) : Prop :=
  ∀ j : ℤ,PadicLower p (w-s*j) (rationalCoefficientAt a j f)

theorem ScaledLaurentPadicLower.mul {a : ℚ} {s w v : ℤ} {f g : RatFunc ℚ}
    (hf : ScaledLaurentPadicLower p a s w f) (hg : ScaledLaurentPadicLower p a s v g) :
    ScaledLaurentPadicLower p a s (w+v) (f*g) := by
  intro j
  change PadicLower p (w+v-s*j) ((rationalLaurentAt a (f*g)).coeff j)
  rw [map_mul,HahnSeries.coeff_mul]
  apply padicLower_sum
  intro ij hij
  have he : ij.1+ij.2=j := (Finset.mem_antidiagonal.mp hij).2.2
  convert (hf ij.1).mul (hg ij.2) using 1 <;> try rfl
  rw [← he]
  ring

theorem ScaledLaurentPadicLower.constant {a q : ℚ} {s w : ℤ} (hq : PadicLower p w q) :
    ScaledLaurentPadicLower p a s w (RatFunc.C q) := by
  intro j
  change PadicLower p (w-s*j) ((rationalLaurentAt a (RatFunc.C q)).coeff j)
  rw [rationalLaurentAt_C,HahnSeries.C_apply]
  by_cases hj : j=0
  · simpa [hj] using hq
  · simp [hj,PadicLower]

theorem ScaledLaurentPadicLower.one (a : ℚ) (s : ℤ) : ScaledLaurentPadicLower p a s 0 1 := by
  simpa using (ScaledLaurentPadicLower.constant (a:=a) (s:=s) (PadicLower.natCast (p:=p) 1))

theorem ScaledLaurentPadicLower.pow {a : ℚ} {s w : ℤ} {f : RatFunc ℚ}
    (hf : ScaledLaurentPadicLower p a s w f) (m : ℕ) :
    ScaledLaurentPadicLower p a s ((m:ℤ)*w) (f^m) := by
  induction m with
  | zero => simpa using ScaledLaurentPadicLower.one (p:=p) a s
  | succ m ih => simpa [pow_succ,add_mul] using ih.mul hf

theorem ScaledLaurentPadicLower.prod {ι : Type*} (S : Finset ι) (a : ℚ) (s : ℤ)
    (w : ι → ℤ) (f : ι → RatFunc ℚ)
    (hf : ∀ i∈S,ScaledLaurentPadicLower p a s (w i) (f i)) :
    ScaledLaurentPadicLower p a s (∑ i∈S,w i) (∏ i∈S,f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using ScaledLaurentPadicLower.one (p:=p) a s
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi]
    exact (hf i (by simp)).mul (ih (fun j hj => hf j (by simp [hj])))

def truncatedRootValuation (p B : ℕ) (z : ℤ) : ℤ :=
  if z=0 then B else padicValNat p z.natAbs

theorem truncatedRootValuation_bounds (B : ℕ) (z : ℤ) (hz : z.natAbs≤p^B) :
    0≤truncatedRootValuation p B z ∧ truncatedRootValuation p B z≤B := by
  unfold truncatedRootValuation
  split_ifs with h
  · omega
  have hv : padicValNat p z.natAbs≤B := by
    have hd := Nat.le_of_dvd (Int.natAbs_pos.mpr h) (pow_padicValNat_dvd (p:=p) (n:=z.natAbs))
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp (hd.trans hz)
  exact ⟨Int.natCast_nonneg _,by exact_mod_cast hv⟩

theorem scaledLinearFactor_laurent (B : ℕ) (a t u : ℤ)
    (hw : truncatedRootValuation p B (u*a-t)≤B) :
    ScaledLaurentPadicLower p (a:ℚ) B (truncatedRootValuation p B (u*a-t))
      (algebraMap ℚ[X] (RatFunc ℚ) (C (u:ℚ)*X-C (t:ℚ))) := by
  intro j
  cases j with
  | negSucc k =>
    rw [rationalCoefficientAt_polynomial_neg _ _ _ (by omega)]
    exact PadicLower.zero _
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast]
    rw [rationalCoefficientAt_polynomial]
    by_cases hk : k=0
    · subst k
      simp only [taylor_coeff_zero,eval_sub,eval_mul,eval_C,eval_X,Int.natCast_zero,mul_zero,sub_zero]
      by_cases hz : u*a-t=0
      · left
        exact_mod_cast hz
      · right
        rw [← Int.cast_mul,← Int.cast_sub,padicValRat.of_int]
        simp [truncatedRootValuation,hz,padicValInt]
    · by_cases hk1 : k=1
      · subst k
        simp only [map_sub,taylor_mul,taylor_C,taylor_X,mul_add,coeff_add,
          coeff_mul_X,coeff_C_zero,coeff_C_succ,coeff_sub,coeff_mul_C,zero_mul,add_zero,sub_zero]
        exact (PadicLower.intCast (p:=p) u).mono (by omega)
      · have he : ((C (u:ℚ)*X-C (t:ℚ)).taylor (a:ℚ)).coeff k=0 := by
          simp only [map_sub,taylor_mul,taylor_C,taylor_X,mul_add,coeff_add,coeff_sub,coeff_C_mul,coeff_X,coeff_C,
            hk,Ne.symm hk,hk1,Ne.symm hk1,ite_false,mul_zero,add_zero,sub_zero]
        rw [he]
        exact PadicLower.zero _

theorem inverseLinearFactor_scaledLaurent (B : ℕ) (a t : ℤ)
    (hw : truncatedRootValuation p B (a-t)≤B) :
    ScaledLaurentPadicLower p (a:ℚ) B (-truncatedRootValuation p B (a-t))
      (rationalPole (t:ℚ) 1) := by
  intro j
  by_cases hat : a=t
  · subst t
    rw [rationalCoefficientAt_pole_self]
    by_cases hj : j = -1
    · subst j
      simp [truncatedRootValuation,PadicLower]
    · simp [hj,PadicLower]
  have hat' : (a:ℚ)≠(t:ℚ) := by exact_mod_cast hat
  have hv : padicValRat p ((a:ℚ)-(t:ℚ))=truncatedRootValuation p B (a-t) := by
    rw [← Int.cast_sub,padicValRat.of_int]
    simp [truncatedRootValuation,sub_ne_zero.mpr hat,padicValInt]
  cases j with
  | negSucc k =>
    rw [rationalCoefficientAt_pole_other_neg _ _ _ hat' _ (by omega)]
    exact PadicLower.zero _
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast]
    rw [show (1:ℕ)=0+1 from rfl,rationalCoefficientAt_pole_regular _ _ hat']
    simp only [zero_add,Nat.choose_self,Nat.cast_one,mul_one]
    right
    rw [padicValRat.div (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (sub_ne_zero.mpr hat'))]
    simp only [padicValRat.pow,padicValRat.neg,padicValRat.one,mul_zero,zero_sub,hv]
    push_cast
    nlinarith
end OddZeta.FourValue

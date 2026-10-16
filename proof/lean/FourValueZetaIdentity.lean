import FourValueZetaTail
import FourValueRationalReflection
import FourValueResidueKernel

noncomputable section
namespace OddZeta.FourValue
open Polynomial

theorem rationalReflect_complex_smul (c : ℂ) (f : RatFunc ℂ) :
    rationalReflect (c • f)=c • rationalReflect f := by
  simp only [RatFunc.smul_eq_C_mul,map_mul]
  rw [show rationalReflect (RatFunc.C c)=RatFunc.C c from rationalReflect.commutes c]

def rationalZetaForm (b h : ℕ) : RatFunc ℂ →ₗ[ℂ] ℂ :=
  rationalC b h + ∑ k ∈ Finset.range 10,
    ((-1:ℂ)^h*(Nat.choose (k+h) h:ℂ)*riemannZeta ((k+h+1:ℕ):ℂ)) • rationalB b (k+1)

theorem rationalZetaForm_pole (b h : ℕ) (j : ℤ) (hj : j∈poleWindow b) (k : Fin 10) :
    rationalZetaForm b h (rationalPole (j:ℂ) (k.val+1)) =
      (-1:ℂ)^h*(Nat.choose (k.val+h) h:ℂ)*
        (riemannZeta ((k.val+h+1:ℕ):ℂ)-finiteHarmonic ((b-j).toNat) (k.val+h+1)) := by
  simp only [rationalZetaForm,LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply,
    smul_eq_mul,rationalC_pole b h j hj k.val k.isLt,
    rationalB_pole b j hj _ _ (Nat.succ_pos _)]
  simp only [Nat.succ_eq_add_one,Nat.add_left_inj,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_range,if_pos k.isLt]
  ring

theorem hasSum_rationalZetaForm (b h : ℕ) (hh : 1≤h)
    (f : RatFunc ℂ) (c : ℤ → Fin 10 → ℂ)
    (hf : f=∑ j ∈ poleWindow b,∑ k : Fin 10,c j k • rationalPole (j:ℂ) (k.val+1)) :
    HasSum (fun r : ℕ => rationalCoefficientAt ((r+b+1:ℕ):ℂ) h f)
      (rationalZetaForm b h f) := by
  have heq : rationalZetaForm b h f = ∑ j ∈ poleWindow b,∑ k : Fin 10,
      c j k*((-1:ℂ)^h*(Nat.choose (k.val+h) h:ℂ)*
        (riemannZeta ((k.val+h+1:ℕ):ℂ)-finiteHarmonic ((b-j).toNat) (k.val+h+1))) := by
    rw [hf,map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_sum,map_smul,smul_eq_mul,rationalZetaForm_pole b h j hj]
  rw [heq]
  exact hasSum_partialFraction_taylor b h hh f c hf

theorem rationalB_reflect_partialFractions (b l : ℕ) (hl : 0<l)
    (f : RatFunc ℂ) (c : ℤ → Fin 10 → ℂ)
    (hf : f=∑ j ∈ poleWindow b,∑ k : Fin 10,c j k • rationalPole (j:ℂ) (k.val+1)) :
    rationalB b l (rationalReflect f)=(-1:ℂ)^l*rationalB b l f := by
  rw [hf]
  simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k _
  have hmj : -j∈poleWindow b := by
    simp only [poleWindow,Finset.mem_Icc] at hj ⊢; omega
  rw [rationalReflect_complex_smul,map_smul,smul_eq_mul,rationalReflect_pole,map_smul,smul_eq_mul,
    show -(j:ℂ)=((-j:ℤ):ℂ) by simp,rationalB_pole b (-j) hmj _ l hl,
    rationalB_pole b j hj _ l hl]
  split_ifs with heq
  · rw [heq]; ring
  · ring

theorem rationalB_even_zero (b l : ℕ) (hl : 0<l) (he : Even l)
    (f : RatFunc ℂ) (ho : rationalReflect f = -f) (c : ℤ → Fin 10 → ℂ)
    (hf : f=∑ j ∈ poleWindow b,∑ k : Fin 10,c j k • rationalPole (j:ℂ) (k.val+1)) :
    rationalB b l f=0 := by
  have H := rationalB_reflect_partialFractions b l hl f c hf
  rw [ho,map_neg,he.neg_one_pow,one_mul] at H
  linear_combination -H/2

/-- The only surviving zeta values are 7,9,11,13; coefficients are Taylor,
not unnormalized fourth-derivative, coefficients. -/
theorem rationalZetaForm_four_values (b : ℕ) (f : RatFunc ℂ)
    (ho : rationalReflect f = -f) (h1 : rationalB b 1 f=0)
    (c : ℤ → Fin 10 → ℂ)
    (hf : f=∑ j ∈ poleWindow b,∑ k : Fin 10,c j k • rationalPole (j:ℂ) (k.val+1)) :
    rationalZetaForm b 4 f = rationalC b 4 f +
      15*riemannZeta 7*rationalB b 3 f + 70*riemannZeta 9*rationalB b 5 f +
      210*riemannZeta 11*rationalB b 7 f + 495*riemannZeta 13*rationalB b 9 f := by
  have h2 := rationalB_even_zero b 2 (by decide) (by decide) f ho c hf
  have h4 := rationalB_even_zero b 4 (by decide) (by decide) f ho c hf
  have h6 := rationalB_even_zero b 6 (by decide) (by decide) f ho c hf
  have h8 := rationalB_even_zero b 8 (by decide) (by decide) f ho c hf
  have h10 := rationalB_even_zero b 10 (by decide) (by decide) f ho c hf
  norm_num [rationalZetaForm,Finset.sum_range_succ,h1,h2,h4,h6,h8,h10,Nat.choose]
  ring

end OddZeta.FourValue

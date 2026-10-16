import FourValueResidueArithmetic
import Mathlib.Data.Int.CardIntervalMod

noncomputable section
namespace OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

theorem centeredResidueCount_floor (a : ℤ) (b : ℕ) :
    centeredResidueCount p a b = ((b:ℤ)+a)/(p:ℤ)+((b:ℤ)-a)/(p:ℤ)+1 := by
  have hp : 0<(p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [centeredResidueCount_eq_card]
  have he : (poleWindow b).filter (fun t => (p:ℤ)∣a-t) =
      (Finset.Ioc (-(b:ℤ)-1) (b:ℤ)).filter (fun t => t ≡ a [ZMOD (p:ℤ)]) := by
    ext t
    simp only [Finset.mem_filter, poleWindow, Finset.mem_Icc, Finset.mem_Ioc,
      Int.modEq_iff_dvd]
    omega
  rw [he, Int.Ioc_filter_modEq_card _ _ hp]
  have hf (x : ℤ) : ⌊(x:ℚ)/(p:ℚ)⌋ = x/(p:ℤ) := Rat.floor_intCast_div_natCast x p
  have he1 : (((b:ℤ):ℚ)-(a:ℚ))/(p:ℚ) = (((b:ℤ)-a:ℤ):ℚ)/(p:ℚ) := by push_cast; rfl
  have he2 : (((-(b:ℤ)-1):ℚ)-(a:ℚ))/(p:ℚ) = (((-(b:ℤ)-1-a:ℤ):ℚ))/(p:ℚ) := by push_cast; ring
  simp only [Int.cast_natCast] at he1 he2
  simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one]
  rw [he1, he2, hf, hf]
  have hn : 0 ≤ ((b:ℤ)-a)/(p:ℤ)-(-(b:ℤ)-1-a)/(p:ℤ) := by
    have h := Int.ediv_le_ediv hp (show -(b:ℤ)-1-a≤(b:ℤ)-a by omega)
    omega
  rw [max_eq_left hn]
  have hd : (-(b:ℤ)-1-a)/(p:ℤ) = -(((b:ℤ)+a)/(p:ℤ))-1 := by
    apply (Int.ediv_eq_iff_of_pos hp).mpr
    have h1 := Int.ediv_mul_le ((b:ℤ)+a) hp.ne'
    have h2 := Int.lt_ediv_add_one_mul_self ((b:ℤ)+a) hp
    constructor <;> nlinarith
  rw [hd]
  ring

/-- The exact lambda in (43), expressed through integer floors. -/
def targetResidueLambda (p n : ℕ) (r : ℤ) : ℤ :=
  targetNormalizationFloor p n +
    5*((100*(n:ℤ)+r)/(p:ℤ)+(100*(n:ℤ)-r)/(p:ℤ)+1) -
      ∑ i : Fin 15, (((targetEndpointTuple n i:ℤ)+r)/(p:ℤ)+
        ((targetEndpointTuple n i:ℤ)-r)/(p:ℤ)+1)

theorem targetLocalWeight_floor_nonzero (n : ℕ) (r : ℤ) (hr : ¬(p:ℤ)∣r) :
    targetLocalWeight p n r = targetResidueLambda p n r := by
  have h0 : rootResidueWeight p r = 0 := by
    simp [rootResidueWeight, ← Int.natCast_dvd, hr]
  simp [targetLocalWeight, h0, centeredResidueCount_floor, targetResidueLambda]
end OddZeta.FourValue

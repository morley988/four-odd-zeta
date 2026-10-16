import FourValueBasisMasses

noncomputable section
namespace OddZeta.FourValue

def basisLimit : ℝ := 361/200

def basisKnot (k : ℕ) : ℝ :=
  if k=0 then 0 else if k=41 then basisLimit else basisLimit*(2*(k:ℝ)-1)/80

def basisKnotWeight (k : ℕ) : Fin 45→ℝ := certificateWeight ⟨min (k-1) 39,by omega⟩
def basisInterval (s : ℝ) : ℕ := ⌊40*s/basisLimit+1/2⌋₊

theorem basisKnot_nonneg (k : ℕ) : 0≤basisKnot k := by
  unfold basisKnot basisLimit
  split_ifs with h0 h41
  · exact le_rfl
  · norm_num
  · have hk : (1:ℝ)≤k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    linarith

theorem basisKnot_strict (k : ℕ) (hk : k≤40) : basisKnot k<basisKnot (k+1) := by
  by_cases h0 : k=0
  · subst k; norm_num [basisKnot,basisLimit]
  by_cases h40 : k=40
  · subst k; norm_num [basisKnot,basisLimit]
  have hk41 : k≠41 := by omega
  have hs0 : k+1≠0 := by omega
  have hs41 : k+1≠41 := by omega
  simp only [basisKnot,if_neg h0,if_neg hk41,if_neg hs0,if_neg hs41,basisLimit]
  push_cast
  linarith

theorem basisInterval_le (s : ℝ) (hs0 : 0≤s) (hs1 : s≤basisLimit) : basisInterval s≤40 := by
  unfold basisInterval
  apply Nat.le_of_lt_succ
  apply (Nat.floor_lt (show 0≤40*s/basisLimit+1/2 by unfold basisLimit; positivity)).mpr
  unfold basisLimit at hs1 ⊢
  norm_num
  linarith

theorem basisInterval_brackets (s : ℝ) (hs0 : 0≤s) (hs1 : s≤basisLimit) :
    basisKnot (basisInterval s)≤s ∧ s≤basisKnot (basisInterval s+1) := by
  have hk := basisInterval_le s hs0 hs1
  have hf := Nat.floor_le (show 0≤40*s/basisLimit+1/2 by unfold basisLimit; positivity)
  have hc := Nat.lt_floor_add_one (40*s/basisLimit+1/2)
  change (basisInterval s:ℝ)≤40*s/basisLimit+1/2 at hf
  change 40*s/basisLimit+1/2<(basisInterval s:ℝ)+1 at hc
  constructor
  · by_cases h0 : basisInterval s=0
    · simpa [basisKnot,h0] using hs0
    · have h41 : basisInterval s≠41 := by omega
      simp only [basisKnot,if_neg h0,if_neg h41,basisLimit]
      unfold basisLimit at hf
      linarith
  · by_cases h40 : basisInterval s=40
    · simpa [basisKnot,h40] using hs1
    · have h0 : basisInterval s+1≠0 := by omega
      have h41 : basisInterval s+1≠41 := by omega
      simp only [basisKnot,if_neg h0,if_neg h41,basisLimit]
      push_cast
      unfold basisLimit at hc
      linarith

def basisInterpolationParameter (s : ℝ) : ℝ :=
  (s-basisKnot (basisInterval s))/(basisKnot (basisInterval s+1)-basisKnot (basisInterval s))

theorem basisInterpolationParameter_bounds (s : ℝ) (hs0 : 0≤s) (hs1 : s≤basisLimit) :
    0≤basisInterpolationParameter s ∧ basisInterpolationParameter s≤1 := by
  have hd := sub_pos.mpr (basisKnot_strict _ (basisInterval_le s hs0 hs1))
  obtain ⟨hl,hr⟩ := basisInterval_brackets s hs0 hs1
  unfold basisInterpolationParameter
  constructor
  · exact div_nonneg (sub_nonneg.mpr hl) hd.le
  · apply (div_le_one hd).mpr
    linarith

theorem basisInterpolationParameter_mass (s : ℝ) (hs0 : 0≤s) (hs1 : s≤basisLimit) :
    (1-basisInterpolationParameter s)*basisKnot (basisInterval s)+
      basisInterpolationParameter s*basisKnot (basisInterval s+1)=s := by
  have hd := ne_of_gt (sub_pos.mpr (basisKnot_strict _ (basisInterval_le s hs0 hs1)))
  unfold basisInterpolationParameter
  field_simp
  ring

def concreteBasisWeight (s : ℝ) (l : Fin 45) : ℝ :=
  if s≤0 then certificateWeight 0 l else
    interpolatedMass (basisKnot (basisInterval s)) (basisKnot (basisInterval s+1))
      (basisInterpolationParameter s) (basisKnotWeight (basisInterval s))
      (basisKnotWeight (basisInterval s+1)) l /s

theorem concreteBasisWeight_nonneg (s : ℝ) (hs0 : 0≤s) (hs1 : s≤basisLimit) (l : Fin 45) :
    0≤concreteBasisWeight s l := by
  unfold concreteBasisWeight
  split_ifs with h0
  · exact certificateWeight_nonneg _ _
  · obtain ⟨ht0,ht1⟩ := basisInterpolationParameter_bounds s hs0 hs1
    apply div_nonneg _ hs0
    exact interpolatedMass_nonneg _ _ _ _ _ (basisKnot_nonneg _) (basisKnot_nonneg _) ht0 ht1
      (certificateWeight_nonneg _) (certificateWeight_nonneg _) l

theorem concreteBasisWeight_sum (s : ℝ) (hs0 : 0≤s) (hs1 : s≤basisLimit) :
    ∑ l : Fin 45,concreteBasisWeight s l=1 := by
  by_cases h0 : s≤0
  · simp only [concreteBasisWeight,if_pos h0]
    exact certificateWeight_sum 0
  · simp only [concreteBasisWeight,if_neg h0,← Finset.sum_div]
    have hw (k : ℕ) : ∑ l,basisKnotWeight k l=1 := certificateWeight_sum _
    rw [interpolatedMass_sum _ _ _ _ _ (hw _) (hw _),
      basisInterpolationParameter_mass s hs0 hs1,div_self (ne_of_gt (lt_of_not_ge h0))]
end OddZeta.FourValue

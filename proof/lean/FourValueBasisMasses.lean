import FourValueConcreteBasis

noncomputable section
namespace OddZeta.FourValue

/-- A dependent cast makes every lookup come with its checked row length. -/
def certificateWeightRow (r : Fin 40) : List ℕ :=
  Certificate.weightRows.get ⟨r.val,by simpa [Certificate.row_count] using r.isLt⟩

theorem certificateWeightRow_length (r : Fin 40) : (certificateWeightRow r).length=45 :=
  (Certificate.rows_valid _ (List.get_mem _ _)).1

theorem certificateWeightRow_sum (r : Fin 40) : (certificateWeightRow r).sum=100000000 :=
  (Certificate.rows_valid _ (List.get_mem _ _)).2

def certificateWeight (r : Fin 40) (l : Fin 45) : ℝ :=
  ((certificateWeightRow r).get ⟨l.val,by rw [certificateWeightRow_length]; exact l.isLt⟩:ℝ)/100000000

theorem certificateWeight_nonneg (r : Fin 40) (l : Fin 45) : 0≤certificateWeight r l := by
  unfold certificateWeight
  positivity

theorem certificateWeight_sum (r : Fin 40) : ∑ l : Fin 45,certificateWeight r l=1 := by
  have hget : (∑ l : Fin 45,(certificateWeightRow r).get
      ⟨l.val,by rw [certificateWeightRow_length]; exact l.isLt⟩)=100000000 := by
    change (∑ l : Fin 45, (certificateWeightRow r).get
      ⟨l.val,by rw [certificateWeightRow_length]; exact l.isLt⟩)=100000000
    calc
      _ = ∑ l : Fin (certificateWeightRow r).length,(certificateWeightRow r).get l :=
        Finset.sum_equiv (finCongr (certificateWeightRow_length r).symm) (fun _ => by simp) (fun _ _ => rfl)
      _ = _ := by rw [← List.sum_ofFn,List.ofFn_get,certificateWeightRow_sum]
  unfold certificateWeight
  rw [← Finset.sum_div]
  have hc : (∑ l : Fin 45,((certificateWeightRow r).get
      ⟨l.val,by rw [certificateWeightRow_length]; exact l.isLt⟩:ℝ))=100000000 := by exact_mod_cast hget
  rw [hc]
  norm_num

/-- Interpolate masses, not normalized weights; this preserves their total mass. -/
def interpolatedMass {ι : Type*} (s₀ s₁ t : ℝ) (w₀ w₁ : ι→ℝ) (l : ι) : ℝ :=
  (1-t)*s₀*w₀ l+t*s₁*w₁ l

theorem interpolatedMass_nonneg {ι : Type*} (s₀ s₁ t : ℝ) (w₀ w₁ : ι→ℝ)
    (hs₀ : 0≤s₀) (hs₁ : 0≤s₁) (ht₀ : 0≤t) (ht₁ : t≤1)
    (hw₀ : ∀ l,0≤w₀ l) (hw₁ : ∀ l,0≤w₁ l) (l : ι) :
    0 ≤ interpolatedMass s₀ s₁ t w₀ w₁ l := by
  have h0 := hw₀ l
  have h1 := hw₁ l
  unfold interpolatedMass
  positivity

theorem interpolatedMass_sum {ι : Type*} [Fintype ι] (s₀ s₁ t : ℝ) (w₀ w₁ : ι→ℝ)
    (hw₀ : ∑ l,w₀ l=1) (hw₁ : ∑ l,w₁ l=1) :
    ∑ l,interpolatedMass s₀ s₁ t w₀ w₁ l=(1-t)*s₀+t*s₁ := by
  simp [interpolatedMass,Finset.sum_add_distrib,← Finset.mul_sum,hw₀,hw₁]

theorem interpolatedMass_potential {ι : Type*} [Fintype ι] (s₀ s₁ t : ℝ)
    (w₀ w₁ K : ι→ℝ) :
    ∑ l,interpolatedMass s₀ s₁ t w₀ w₁ l*K l=
      (1-t)*(s₀*∑ l,w₀ l*K l)+t*(s₁*∑ l,w₁ l*K l) := by
  simp only [interpolatedMass,add_mul,Finset.sum_add_distrib]
  simp only [mul_assoc,← Finset.mul_sum]

theorem interpolatedMass_upper {ι : Type*} [Fintype ι] (s₀ s₁ t G V₀ V₁ : ℝ)
    (w₀ w₁ K : ι→ℝ) (ht₀ : 0≤t) (ht₁ : t≤1)
    (h₀ : G+s₀*(∑ l,w₀ l*K l)≤V₀) (h₁ : G+s₁*(∑ l,w₁ l*K l)≤V₁) :
    G+(∑ l,interpolatedMass s₀ s₁ t w₀ w₁ l*K l)≤(1-t)*V₀+t*V₁ := by
  rw [interpolatedMass_potential]
  have h0 := mul_le_mul_of_nonneg_left h₀ (show 0≤1-t by linarith)
  have h1 := mul_le_mul_of_nonneg_left h₁ ht₀
  nlinarith
end OddZeta.FourValue

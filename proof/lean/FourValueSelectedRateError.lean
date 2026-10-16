import FourValueUniformDensity

noncomputable section
namespace OddZeta.FourValue

theorem factorialRowRate_lower (s : ℝ) (hs : 0≤s) (hs1 : s≤basisLimit) : -24≤factorialRowRate s := by
  by_cases hs0 : s=0
  · simp [hs0,factorialRowRate]
  have hspos : 0<s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hs2 : s≤2 := by unfold basisLimit at hs1; linarith
  have hl := Real.log_le_log (show 0<2*s by positivity) (show 2*s≤4 by linarith)
  have hlog4 : Real.log 4≤3 := by have h := Real.log_le_sub_one_of_pos (show (0:ℝ)<4 by norm_num); linarith
  have hm := mul_le_mul_of_nonneg_left (le_trans hl hlog4) (show 0≤4*s by positivity)
  unfold factorialRowRate
  nlinarith

theorem selected_real_sum_le_total {m k : ℕ} (r : Fin k ↪ Fin (m+1))
    (f : Fin (m+1)→ℝ) (L : ℝ) (hf : ∀ j,L≤f j) :
    (∑ i,f (r i))≤(∑ j,f j)-((m+1-k:ℕ):ℝ)*L := by
  classical
  let S := Finset.univ.map r
  have hS : S.card=k := by simp [S]
  have hpart := Finset.sum_sdiff (s₁:=S) (s₂:=Finset.univ) (f:=f) (Finset.subset_univ _)
  have hcard : (Finset.univ\S).card=m+1-k := by rw [Finset.card_sdiff]; simp [hS]
  have hb : ((m+1-k:ℕ):ℝ)*L≤∑ j∈Finset.univ\S,f j := by
    calc
      _ = ∑ j∈Finset.univ\S,L := by simp [hcard]
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hf j)
  have hsum : (∑ j∈S,f j)=∑ i,f (r i) := by simp [S]
  rw [hsum] at hpart
  linarith

theorem selected_real_sum_codim_four {m : ℕ} (hm : 3≤m) (r : Fin (m+1-4) ↪ Fin (m+1))
    (f : Fin (m+1)→ℝ) (L : ℝ) (hf : ∀ j,L≤f j) :
    (∑ i,f (r i))≤(∑ j,f j)-4*L := by
  have h := selected_real_sum_le_total r f L hf
  have he : m+1-(m+1-4)=4 := by omega
  simpa only [he,Nat.cast_ofNat] using h

theorem selected_contour_rate_sum_bound (n : ℕ) (hn : 1≤n) (V : ℝ→ℝ) (L : ℝ)
    (hV : ∀ s : ℝ,0≤s → s≤basisLimit → L≤V s)
    (r : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1)) :
    (∑ i,(V (adaptedIndexMass n (r i).val)+factorialRowRate (adaptedIndexMass n (r i).val)))≤
      (∑ j : Fin (targetHankelDegree n+1),(V (adaptedIndexMass n j.val)+factorialRowRate (adaptedIndexMass n j.val)))-
      4*(L-24) := by
  apply selected_real_sum_codim_four (by unfold targetHankelDegree; omega) r (fun j => V (adaptedIndexMass n j.val)+factorialRowRate (adaptedIndexMass n j.val)) (L-24)
  intro j
  have hs := adaptedIndexMass_bounds n j.val hn (by omega)
  linarith [hV _ hs.1 hs.2,factorialRowRate_lower _ hs.1 hs.2]
end OddZeta.FourValue

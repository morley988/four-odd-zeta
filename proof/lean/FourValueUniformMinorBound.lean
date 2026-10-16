import FourValueUniformContourSize
import FourValueSelectedRateError

noncomputable section
namespace OddZeta.FourValue
open Polynomial

def contourRowRate (V : ℝ→ℝ) (s : ℝ) : ℝ := V s+factorialRowRate s

theorem half_rate_sum {k : ℕ} (f : Fin k→ℝ) (M B : ℝ) :
    (∑ i,(M*f i+B)/2)=(M/2)*(∑ i,f i)+(k:ℝ)*B/2 := by
  rw [← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem actualAdaptedZetaMatrix_uniform_minor_bound (L : ℝ) : ∃ D : ℝ,1≤D ∧
    ∀ n : ℕ,1≤n → ∀ V : ℝ→ℝ,
      (∀ s : ℝ,0≤s → s≤basisLimit → L≤V s) →
      (∀ s y : ℝ,0≤s → s≤basisLimit → 0<y → contourRate s y≤V s) →
      ∀ rows cols : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1),
      ‖((actualAdaptedZetaMatrix n).submatrix rows cols).det‖≤
        (Nat.factorial (targetHankelDegree n+1-4):ℝ)*
          Real.exp ((100*(n:ℝ))*(∑ j : Fin (targetHankelDegree n+1),contourRowRate V (adaptedIndexMass n j.val))-
            4*(100*(n:ℝ))*(L-24)+(targetHankelDegree n+1-4:ℕ)*(Real.log (100*(n:ℝ))+Real.log D)) := by
  obtain ⟨D,hD,hsize⟩ := actualContourSize_uniform_bound L
  refine ⟨D,hD,?_⟩
  intro n hn V hV hcert rows cols
  let M : ℝ := 100*(n:ℝ)
  let k := targetHankelDegree n+1-4
  let f : Fin (targetHankelDegree n+1)→ℝ := fun j => contourRowRate V (adaptedIndexMass n j.val)
  let B := Real.log M+Real.log D
  have hM : 0<M := by dsimp [M]; exact_mod_cast (show 0<100*n by omega)
  have heach (j : Fin (targetHankelDegree n+1)) : analyticContourSize n (actualAdaptedBasis n j.val)≤Real.exp ((M*f j+B)/2) := by
    have hs := adaptedIndexMass_bounds n j.val hn (by omega)
    have h := hsize n j.val hn (by omega) (V (adaptedIndexMass n j.val)) (hV _ hs.1 hs.2)
      (fun y hy => hcert _ y hs.1 hs.2 hy)
    convert h using 1 <;> dsimp [M,f,B,contourRowRate] <;> ring
  have hprod (r : Fin k ↪ Fin (targetHankelDegree n+1)) :
      (∏ i,analyticContourSize n (actualAdaptedBasis n (r i).val))≤
      Real.exp ((M/2)*(∑ i,f (r i))+(k:ℝ)*B/2) := by
    have h := Finset.prod_le_prod (s:=Finset.univ)
      (fun i _ => analyticContourSize_nonneg n (actualAdaptedBasis n (r i).val)) (fun i _ => heach (r i))
    rw [← Real.exp_sum,half_rate_sum] at h
    exact h
  have hrows := selected_contour_rate_sum_bound n hn V L hV rows
  have hcols := selected_contour_rate_sum_bound n hn V L hV cols
  change (∑ i,f (rows i))≤(∑ j,f j)-4*(L-24) at hrows
  change (∑ i,f (cols i))≤(∑ j,f j)-4*(L-24) at hcols
  have hexp : ((M/2)*(∑ i,f (rows i))+(k:ℝ)*B/2)+((M/2)*(∑ i,f (cols i))+(k:ℝ)*B/2)≤
      M*(∑ j,f j)-4*M*(L-24)+(k:ℝ)*B := by
    have h := mul_le_mul_of_nonneg_left (add_le_add hrows hcols) (show 0≤M/2 by positivity)
    nlinarith only [h]
  have hdet := actualAdaptedZetaMatrix_minor_bound n hn k rows cols
  calc
    _ ≤ (Nat.factorial k:ℝ)*(∏ i,analyticContourSize n (actualAdaptedBasis n (rows i).val))*
        (∏ i,analyticContourSize n (actualAdaptedBasis n (cols i).val)) := hdet
    _ ≤ (Nat.factorial k:ℝ)*Real.exp ((M/2)*(∑ i,f (rows i))+(k:ℝ)*B/2)*
        Real.exp ((M/2)*(∑ i,f (cols i))+(k:ℝ)*B/2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hprod rows) (by positivity)
      · exact hprod cols
      · exact Finset.prod_nonneg (fun _ _ => analyticContourSize_nonneg _ _)
      · positivity
    _ = (Nat.factorial k:ℝ)*Real.exp (((M/2)*(∑ i,f (rows i))+(k:ℝ)*B/2)+((M/2)*(∑ i,f (cols i))+(k:ℝ)*B/2)) := by rw [mul_assoc,← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
end OddZeta.FourValue

import FourValuePhysicalRootBounds
import FourValueMonicBasisChange
import FourValueLargeMinorBounds

noncomputable section
namespace OddZeta.FourValue
open Polynomial

def adaptedMonicTransition (n : ℕ) :
    Matrix (Fin (targetHankelDegree n+1)) (Fin (targetHankelDegree n+1)) ℂ :=
  monicBasisTransition (fun i => actualAdaptedMonic n i.val) (fun i => squareRootProduct i.val)

theorem adaptedMonicTransition_triangular (n : ℕ) (hn : 1≤n) :
    (adaptedMonicTransition n).IsUpperTriangular :=
  monicBasisTransition_triangular _ _ (fun i => actualAdaptedMonic_monic n i.val hn (by omega))
    (fun i => actualAdaptedMonic_natDegree n i.val hn (by omega)) (fun i => squareRootProduct_degree i.val)

def analyticTransitionBase (n : ℕ) : ℝ :=
  ((targetHankelDegree n+1:ℕ):ℝ)^2*analyticRootRadius n

theorem analyticTransitionBase_ge_one (n : ℕ) (hn : 1≤n) : 1≤analyticTransitionBase n := by
  have hN : (1:ℝ)≤(targetHankelDegree n+1:ℕ) := by exact_mod_cast (show 1≤targetHankelDegree n+1 by omega)
  have hM : (1:ℝ)≤(100*n:ℕ) := by exact_mod_cast (show 1≤100*n by omega)
  unfold analyticTransitionBase analyticRootRadius
  nlinarith [sq_nonneg (((targetHankelDegree n+1:ℕ):ℝ)),sq_nonneg (((100*n:ℕ):ℝ)),
    mul_le_mul (show (1:ℝ)≤((targetHankelDegree n+1:ℕ):ℝ)^2 by nlinarith)
      (show (1:ℝ)≤((100*n:ℕ):ℝ)^2 by nlinarith) (by norm_num : (0:ℝ)≤1) (by positivity)]

theorem adaptedMonicTransition_bound (n : ℕ) (hn : 1≤n)
    (i j : Fin (targetHankelDegree n+1)) (hij : i≤j) :
    ‖adaptedMonicTransition n i j‖≤((targetHankelDegree n+1:ℕ):ℝ)*
      (analyticTransitionBase n)^(j.val-i.val) :=
  monicBasisTransition_bound _ _ (fun i => actualAdaptedMonic_monic n i.val hn (by omega))
    (fun i => squareRootProduct_monic i.val)
    (fun i => actualAdaptedMonic_natDegree n i.val hn (by omega))
    (fun i => squareRootProduct_degree i.val) (analyticRootRadius n) (analyticRootRadius_pos n hn)
    (fun i z hz => actualAdaptedMonic_common_root_bound n i.val hn z hz)
    (fun i z hz => squareRootProduct_common_root_bound n i.val (by omega) z hz) i j hij

def squareBasisMultiplier (j : ℕ) : ℂ := if j=0 then 1 else 2

def adaptedToSquare (n : ℕ) :
    Matrix (Fin (targetHankelDegree n+1)) (Fin (targetHankelDegree n+1)) ℂ := fun i j =>
  (Nat.factorial (2*i.val):ℂ)*adaptedMonicTransition n i j*
    (squareBasisMultiplier j.val/(Nat.factorial (2*j.val):ℂ))

theorem squareBasisMultiplier_norm (j : ℕ) : ‖squareBasisMultiplier j‖≤2 := by
  unfold squareBasisMultiplier
  split_ifs <;> norm_num

theorem adaptedToSquare_triangular (n : ℕ) (hn : 1≤n) : (adaptedToSquare n).IsUpperTriangular := by
  intro i j hij
  simp [adaptedToSquare,adaptedMonicTransition_triangular n hn hij]

theorem adaptedToSquare_bound (n : ℕ) (hn : 1≤n)
    (i j : Fin (targetHankelDegree n+1)) (hij : i≤j) :
    ‖adaptedToSquare n i j‖≤(2*((targetHankelDegree n+1:ℕ):ℝ))*
      (analyticTransitionBase n)^(j.val-i.val) := by
  have hD0 : 0≤analyticTransitionBase n := (by linarith [analyticTransitionBase_ge_one n hn])
  have hfi : (0:ℝ)<Nat.factorial (2*i.val) := by exact_mod_cast Nat.factorial_pos _
  have hfj : (0:ℝ)<Nat.factorial (2*j.val) := by exact_mod_cast Nat.factorial_pos _
  have hfij : (Nat.factorial (2*i.val):ℝ)≤Nat.factorial (2*j.val) := by
    exact_mod_cast Nat.factorial_le (Nat.mul_le_mul_left 2 hij)
  rw [adaptedToSquare,norm_mul,norm_mul,norm_div,Complex.norm_natCast,Complex.norm_natCast]
  calc
    _ ≤ (Nat.factorial (2*i.val):ℝ)*(((targetHankelDegree n+1:ℕ):ℝ)*
        (analyticTransitionBase n)^(j.val-i.val))*(2/(Nat.factorial (2*j.val):ℝ)) := by
      gcongr
      · exact adaptedMonicTransition_bound n hn i j hij
      · exact squareBasisMultiplier_norm j.val
    _ ≤ (Nat.factorial (2*j.val):ℝ)*(((targetHankelDegree n+1:ℕ):ℝ)*
        (analyticTransitionBase n)^(j.val-i.val))*(2/(Nat.factorial (2*j.val):ℝ)) := by
      gcongr
    _ = _ := by field_simp

theorem adaptedToSquare_large_minor_bound (n : ℕ) (hn : 1≤n)
    (r c : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1)) :
    ‖((adaptedToSquare n).submatrix r c).det‖≤
      (Nat.factorial (targetHankelDegree n+1-4):ℝ)*
      (2*((targetHankelDegree n+1:ℕ):ℝ))^(targetHankelDegree n+1-4)*
      (analyticTransitionBase n)^(4*targetHankelDegree n) :=
  upper_triangular_four_omitted_bound _ (adaptedToSquare_triangular n hn) _ _ (by positivity)
    (analyticTransitionBase_ge_one n hn) (adaptedToSquare_bound n hn) r c
end OddZeta.FourValue

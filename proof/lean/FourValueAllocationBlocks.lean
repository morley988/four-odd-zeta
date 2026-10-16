import FourValueAllocationDual
import Mathlib.LinearAlgebra.Matrix.Block

noncomputable section
namespace OddZeta.FourValue.Allocation
open Finset Matrix
variable {p : ℕ} [Fact p.Prime]

/-- All square minors, including repeated row/column choices. -/
def MinorLower {ι : Type*} (A : Matrix ι ι ℚ) (bound : ℕ → ℤ) : Prop :=
 ∀ m, ∀ rows cols : Fin m → ι, PadicLower p (bound m) (A.submatrix rows cols).det

theorem minorLower_reindex {ι κ : Type*} [Fintype κ] [DecidableEq κ]
 (A : Matrix ι ι ℚ) (bound : ℕ → ℤ) (h : MinorLower (p:=p) A bound)
 (rows cols : κ → ι) : PadicLower p (bound (Fintype.card κ)) (A.submatrix rows cols).det := by
 let e := Fintype.equivFin κ
 have hh := h (Fintype.card κ) (rows ∘ e.symm) (cols ∘ e.symm)
 simpa only [← Matrix.submatrix_submatrix,Matrix.det_submatrix_equiv_self] using hh

/-- Block diagonal sum of the local matrices. -/
def blockMatrix {d n : ℕ} (A : Fin d → Matrix (Fin n) (Fin n) ℚ) :
 Matrix (Fin d × Fin n) (Fin d × Fin n) ℚ :=
 fun i j => if i.1=j.1 then A i.1 i.2 j.2 else 0

theorem blockMinor_lower {d n k : ℕ} (A : Fin d → Matrix (Fin n) (Fin n) ℚ)
 (price : ℤ) (pen : Fin d → ℤ)
 (hlocal : ∀ a, MinorLower (p:=p) (A a) (fun m => price*m-pen a))
 (rows cols : Fin k → Fin d × Fin n) :
 PadicLower p (price*k-∑ a,pen a) ((blockMatrix A).submatrix rows cols).det := by
 classical
 let M := (blockMatrix A).submatrix rows cols
 by_cases hz : M.det=0
 · exact Or.inl hz
 have hs : (∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ * ∏ i, M (σ i) i) ≠ 0 := by
   simpa only [Matrix.det_apply'] using hz
 obtain ⟨σ,hσ,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
 have he (i : Fin k) : (rows (σ i)).1=(cols i).1 := by
   have hp : (∏ j, M (σ j) j) ≠ 0 := (mul_ne_zero_iff.mp hne).2
   have hn := (Finset.prod_ne_zero_iff.mp hp) i (mem_univ _)
   by_contra hh
   exact hn (by simp [M,blockMatrix,hh])
 let B := M.submatrix σ id
 let label := fun i : Fin k => (cols i).1
 have hb : B.BlockTriangular label := by
   intro i j hij
   have hh : (rows (σ i)).1 ≠ (cols j).1 := by rw [he]; exact ne_of_gt hij
   simp [B,M,blockMatrix,hh]
 have hdet := hb.det_fintype
 have hblock (a : Fin d) :
   PadicLower p (price*(Fintype.card {i : Fin k // label i=a})-pen a)
     (B.toSquareBlock label a).det := by
   have hh := minorLower_reindex (A a) _ (hlocal a)
     (fun i : {i : Fin k // label i=a} => (rows (σ i.val)).2)
     (fun i : {i : Fin k // label i=a} => (cols i.val).2)
   convert hh using 1
   congr 1
   ext i j
   have hi : (rows (σ i.val)).1=a := (he i.val).trans i.property
   have hj : (cols j.val).1=a := j.property
   simp [Matrix.toSquareBlock_def,B,M,blockMatrix,hi,hj]
 have hp := padicLower_prod (p:=p) univ (fun a => (B.toSquareBlock label a).det)
   (fun a => price*(Fintype.card {i : Fin k // label i=a})-pen a) (fun a _ => hblock a)
 rw [← hdet] at hp
 have hcard : (∑ a : Fin d,Fintype.card {i : Fin k // label i=a})=k := by
   simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr (Equiv.sigmaFiberEquiv label)
 have hw : (∑ a : Fin d, (price*(Fintype.card {i : Fin k // label i=a}:ℤ)-pen a))=price*k-∑ a,pen a := by
   rw [sum_sub_distrib,← mul_sum,← Nat.cast_sum,hcard]
 rw [hw] at hp
 rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
 · simpa [B,Matrix.det_permute,hs] using hp
 · simpa [B,Matrix.det_permute,hs] using hp.neg

/-- Rectangular determinant expansion on arbitrary finite index types. -/
theorem rectangular_expansion {ι κ : Type*} [Fintype ι] [DecidableEq ι]
 [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℚ) (B : Matrix κ ι ℚ) :
 (A*B).det=∑ f : ι → κ,(A.submatrix id f).det * ∏ i,B (f i) i := by
 classical
 simp only [Matrix.det_apply',Matrix.mul_apply,Finset.prod_univ_sum,
   Finset.mul_sum,Fintype.piFinset_univ,Matrix.submatrix_apply,id_eq]
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro f _
 rw [Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro σ _
 rw [Finset.prod_mul_distrib,mul_assoc]

theorem right_integral {ι κ : Type*} [Fintype ι] [DecidableEq ι]
 [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℚ) (B : Matrix κ ι ℚ) (w : ℤ)
 (hA : ∀ f : ι → κ,PadicLower p w (A.submatrix id f).det)
 (hB : ∀ i j,PadicLower p 0 (B i j)) : PadicLower p w (A*B).det := by
 rw [rectangular_expansion]
 apply padicLower_sum
 intro f _
 have hb := padicLower_prod (p:=p) univ (fun i => B (f i) i) (fun _ => (0:ℤ))
   (fun i _ => hB (f i) i)
 simpa using (hA f).mul hb

theorem left_integral {ι κ : Type*} [Fintype ι] [DecidableEq ι]
 [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℚ) (B : Matrix κ ι ℚ) (w : ℤ)
 (hA : ∀ i j,PadicLower p 0 (A i j))
 (hB : ∀ f : ι → κ,PadicLower p w (B.submatrix f id).det) : PadicLower p w (A*B).det := by
 have h := right_integral B.transpose A.transpose w
   (fun f => by simpa only [← Matrix.transpose_submatrix,Matrix.det_transpose] using hB f)
   (fun i j => hA j i)
 simpa only [← Matrix.transpose_mul,Matrix.det_transpose] using h

/-- The global dual allocation bound for a sum of local matrices. The proof
uses square local minors, not the weaker entrywise bound. -/
theorem sum_matrix_dual_lower {d n : ℕ} (A : Fin d → Matrix (Fin n) (Fin n) ℚ)
 (price : ℤ) (pen : Fin d → ℤ)
 (hlocal : ∀ a,MinorLower (p:=p) (A a) (fun m => price*m-pen a)) :
 PadicLower p (price*n-∑ a,pen a) (∑ a,A a).det := by
 classical
 let U : Matrix (Fin n) (Fin d × Fin n) ℚ := fun i j => if i=j.2 then 1 else 0
 let V : Matrix (Fin d × Fin n) (Fin n) ℚ := fun i j => if i.2=j then 1 else 0
 have hu : ∀ i j,PadicLower p 0 (U i j) := by
   intro i j; dsimp [U]; split_ifs <;> simp [PadicLower]
 have hv : ∀ i j,PadicLower p 0 (V i j) := by
   intro i j; dsimp [V]; split_ifs <;> simp [PadicLower]
 have he : (U*blockMatrix A*V : Matrix (Fin n) (Fin n) ℚ)=∑ a,A a := by
   ext i j
   simp only [Matrix.sum_apply]
   change (∑ t, (∑ s,U i s*blockMatrix A s t)*V t j) = ∑ a,A a i j
   simp [U,V,blockMatrix,Fintype.sum_prod_type]
 have h : PadicLower p (price*n-∑ a,pen a) (U*blockMatrix A*V).det := by
   apply right_integral _ V _ _ hv
   intro cols
   have he' : (U*blockMatrix A).submatrix id cols=U*((blockMatrix A).submatrix id cols) := by
     ext i j; simp [Matrix.mul_apply]
   rw [he']
   apply left_integral U _ _ hu
   intro rows
   simpa only [Matrix.submatrix_submatrix,Function.comp_def,id_eq] using
     blockMinor_lower A price pen hlocal rows cols
 simpa only [he] using h

end OddZeta.FourValue.Allocation

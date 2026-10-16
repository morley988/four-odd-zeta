import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Lean

/-! Explicit external-numerics trust boundary. This module is NOT a fully
kernel-certified transcendental certificate. Two finite families below are
assumed, and independently checked by verify_values.py using Arb.
The table is ordinary immutable Lean data, constructed from the exact text
file by an elaborator. The elaborator supplies data, never proofs. -/
namespace OddZeta.FourValue.External

inductive TextTree where
  | leaf : String → TextTree
  | branch : Nat → TextTree → TextTree → TextTree

def TextTree.getFuel : Nat → TextTree → Nat → String
  | 0, _, _ => ""
  | fuel+1, t, i =>
    match t with
    | .leaf s => s
    | .branch n l r => if i < n then getFuel fuel l i else getFuel fuel r (i-n)

def TextTree.get (t : TextTree) (i : Nat) : String := t.getFuel 32 i

open Lean Elab Term in
private partial def makeLiteralTree (xs : Array String) (lo hi : Nat) : TermElabM Expr := do
  if hi-lo=1 then
    return mkApp (mkConst ``TextTree.leaf) (mkStrLit xs[lo]!)
  else
    let mid := (lo+hi)/2
    let l ← makeLiteralTree xs lo mid
    let r ← makeLiteralTree xs mid hi
    return mkApp3 (mkConst ``TextTree.branch) (mkNatLit (mid-lo)) l r

open Lean Elab Term in
private partial def makeTextTree (xs : Array String) (lo hi : Nat) : TermElabM Expr := do
  if hi-lo ≤ 64 then
    let e ← makeLiteralTree xs lo hi
    let name := Name.str `OddZeta.FourValue.External ("valueBlock_" ++ toString lo)
    addDecl (.defnDecl {
      name := name
      levelParams := []
      type := mkConst ``TextTree
      value := e
      hints := .regular 0
      safety := .safe })
    return mkConst name
  else
    let mid := (lo+hi)/2
    let l ← makeTextTree xs lo mid
    let r ← makeTextTree xs mid hi
    return mkApp3 (mkConst ``TextTree.branch) (mkNatLit (mid-lo)) l r

open Lean Elab Term in
elab "external_transcendental_table" : term => do
  let source ← getFileName
  let path := (System.FilePath.mk source).parent.getD "." / ".." / "numerical" / "external26" / "transcendental_values.txt"
  let raw ← IO.FS.readBinFile path
  let count := 6900022
  unless raw.size == 4096+58*count do
    throwError "External table has wrong byte length"
  let mut chunks : Array String := #[]
  for start in [:((count+63)/64)] do
    let lo := 4096+58*(64*start)
    let hi := min raw.size (lo+58*64)
    chunks := chunks.push (String.fromUTF8! (raw.extract lo hi))
  makeTextTree chunks 0 chunks.size

noncomputable def values : TextTree := external_transcendental_table

def digit (s : String) (pos : Nat) : Nat := (String.Pos.Raw.get! s ⟨pos⟩).toNat-48

def digits (s : String) (start len : Nat) : Nat :=
  ((s.toList.drop start).take len).foldl (fun n c => 10*n+(c.toNat-48)) 0

noncomputable def field (row offset len : Nat) : Nat :=
  digits (values.get (row/64)) (58*(row%64)+offset) len

noncomputable def argument (row : Nat) : ℚ := (field row 2 16:ℚ)/(field row 19 16:ℚ)
noncomputable def lowerNumerator (row : Nat) : ℤ :=
  let s := values.get (row/64)
  let n : ℤ := field row 37 20
  if String.Pos.Raw.get! s ⟨58*(row%64)+36⟩ = '-' then -n else n
noncomputable def lower (row : Nat) : ℚ := (lowerNumerator row:ℚ)/1000000000000000000
noncomputable def upper (row : Nat) : ℚ := ((lowerNumerator row:ℚ)+5)/1000000000000000000

def logCount : Nat := 5700022
def atanCount : Nat := 1200000

/-- Exactly the logarithm rows of the shipped finite table; not arbitrary inputs. -/
theorem log_values (i : Fin logCount) :
    (lower i:ℝ) ≤ Real.log (argument i:ℝ) ∧
    Real.log (argument i:ℝ) ≤ (upper i:ℝ) := by
  sorry -- EXTERNAL_TRANSCENDENTAL_VALUE_CERTIFICATION_V1

/-- Exactly the arctangent rows of the shipped finite table; radians. -/
theorem atan_values (i : Fin atanCount) :
    (lower (logCount+i):ℝ) ≤ Real.arctan (argument (logCount+i):ℝ) ∧
    Real.arctan (argument (logCount+i):ℝ) ≤ (upper (logCount+i):ℝ) := by
  sorry -- EXTERNAL_TRANSCENDENTAL_VALUE_CERTIFICATION_V1

end OddZeta.FourValue.External

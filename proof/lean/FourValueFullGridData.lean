import FourValueFullGridExpressions

namespace OddZeta.FourValue.FullGrid
open Lean Elab Term in
private partial def makeLiteralTree (xs : Array String) (lo hi : Nat) : TermElabM Lean.Expr := do
  if hi-lo=1 then
    return mkApp (mkConst ``External.TextTree.leaf) (mkStrLit xs[lo]!)
  else
    let mid := (lo+hi)/2
    let l ← makeLiteralTree xs lo mid
    let r ← makeLiteralTree xs mid hi
    return mkApp3 (mkConst ``External.TextTree.branch) (mkNatLit (mid-lo)) l r

open Lean Elab Term in
private partial def makeGridTree (xs : Array String) (lo hi : Nat) : TermElabM Lean.Expr := do
  if hi-lo ≤ 64 then
    let e ← makeLiteralTree xs lo hi
    let name := Name.str `OddZeta.FourValue.FullGrid ("gridBlock_" ++ toString lo)
    addDecl (.defnDecl {
      name := name
      levelParams := []
      type := mkConst ``External.TextTree
      value := e
      hints := .regular 0
      safety := .safe })
    return mkConst name
  else
    let mid := (lo+hi)/2
    let l ← makeGridTree xs lo mid
    let r ← makeGridTree xs mid hi
    return mkApp3 (mkConst ``External.TextTree.branch) (mkNatLit (mid-lo)) l r

open Lean Elab Term in
elab "external_grid_table" : term => do
  let source ← getFileName
  let path := (System.FilePath.mk source).parent.getD "." / ".." / "numerical" / "fullgrid27" / "grid_arithmetic.txt"
  let raw ← IO.FS.readBinFile path
  let count := 2300000
  unless raw.size == 18*count do
    throwError "External table has wrong byte length"
  let mut chunks : Array String := #[]
  for start in [:((count+63)/64)] do
    let lo := 18*(64*start)
    let hi := min raw.size (lo+18*64)
    chunks := chunks.push (String.fromUTF8! (raw.extract lo hi))
  makeGridTree chunks 0 chunks.size


noncomputable def gridValues : External.TextTree := external_grid_table
noncomputable def gridInt (row : ℕ) : ℤ :=
 let s := gridValues.get (row/64)
 let n : ℤ := External.digits s (18*(row%64)+1) 16
 if String.Pos.Raw.get! s ⟨18*(row%64)⟩ = '-' then -n else n
noncomputable def G (k : Fin 50000) : ℚ := (gridInt (46*k.val):ℚ)/100000000
noncomputable def K (k : Fin 50000) (j : Fin 45) : ℚ := (gridInt (46*k.val+1+j.val):ℚ)/100000000

def uRow (k : Fin 50000) (j : Fin 45) : ℕ := 22+114*k.val+24+2*j.val
def vRow (k : Fin 50000) (j : Fin 45) : ℕ := uRow k j+1
noncomputable def U (k : Fin 50000) (j : Fin 45) : ℚ := External.argument (uRow k j)-17/5000000000
noncomputable def V (k : Fin 50000) (j : Fin 45) : ℚ := External.argument (vRow k j)-17/5000000000
end OddZeta.FourValue.FullGrid

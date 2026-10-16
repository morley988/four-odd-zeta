from pathlib import Path
p=Path('work/Four_Value_Lean_Round20/lean')
s='''import FourValueExternalInterface

noncomputable section
namespace OddZeta.FourValue.FullGrid
open Transcendental

/-- Expressions use rational coefficients and finitely indexed transcendental rows. -/
inductive Expr where
 | rat : ℚ → Expr
 | log : ℕ → ℚ → Expr
 | atan : ℕ → ℚ → Expr
 | pi : Expr
 | add : Expr → Expr → Expr
 | scale : ℚ → Expr → Expr
 | sum (n : ℕ) : (Fin n → Expr) → Expr

def Expr.eval : Expr → ℝ
 | .rat q => q
 | .log _ q => Real.log (q:ℝ)
 | .atan _ q => Real.arctan (q:ℝ)
 | .pi => Real.pi
 | .add a b => a.eval+b.eval
 | .scale q a => (q:ℝ)*a.eval
 | .sum _ f => ∑ i, (f i).eval

def Expr.box : Expr → QInterval
 | .rat q => QInterval.point q
 | .log i _ => ⟨External.lower i,External.upper i⟩
 | .atan i _ => ⟨External.lower (External.logCount+i),External.upper (External.logCount+i)⟩
 | .pi => Batch.piBox
 | .add a b => QInterval.add a.box b.box
 | .scale q a => QInterval.scale q a.box
 | .sum _ f => ⟨∑ i, (f i).box.lo, ∑ i, (f i).box.hi⟩

/-- Only finite rational identities and index bounds: no analytic propositions. -/
def Expr.Valid : Expr → Prop
 | .rat _ => True
 | .log i q => i < External.logCount ∧ External.argument i = q
 | .atan i q => i < External.atanCount ∧ External.argument (External.logCount+i) = q
 | .pi => True
 | .add a b => a.Valid ∧ b.Valid
 | .scale _ a => a.Valid
 | .sum _ f => ∀ i, (f i).Valid

theorem Expr.contains (e : Expr) (h : e.Valid) : e.box.Contains e.eval := by
 induction e with
 | rat q => exact QInterval.point_contains q
 | log i q =>
   have hh := External.log_values ⟨i,h.1⟩
   simpa only [Expr.box,Expr.eval,QInterval.Contains,h.2] using hh
 | atan i q =>
   have hh := External.atan_values ⟨i,h.1⟩
   simpa only [Expr.box,Expr.eval,QInterval.Contains,h.2] using hh
 | pi => exact Batch.piBox_contains
 | add a b ha hb => exact QInterval.add_contains (ha h.1) (hb h.2)
 | scale q a ha => exact QInterval.scale_contains q (ha h)
 | sum n f hf =>
   constructor <;> simp only [Expr.box,Expr.eval,Rat.cast_sum]
   · exact Finset.sum_le_sum (fun i _ => (hf i (h i)).1)
   · exact Finset.sum_le_sum (fun i _ => (hf i (h i)).2)

def left (k : Fin 50000) : ℚ := (k:ℕ)/10000
def right (k : Fin 50000) : ℚ := ((k:ℕ)+1)/10000
def alpha (i : Fin 15) : ℚ := (targetEndpointTuple 1 i:ℚ)/100
def alphaSlot (i : Fin 15) : ℕ := if i.val < 5 then 2 else 2*(i.val-4)+2
def slopeSlot (i : Fin 15) : ℕ := if i.val < 5 then 11 else i.val+7

def jExpr (k : Fin 50000) (slot : ℕ) (a : ℚ) : Expr :=
 let y := right k
 let u := 1+(3/5)*y+a
 .add (.add (.scale (u/2) (.log (22+114*k.val+slot) (u^2+y^2))) (.rat (-u)))
   (.scale y (.atan (24*k.val+slot) (u/y)))

def entropyExpr : Expr :=
 .add (.sum 10 (fun i =>
   let a : ℚ := (2*targetFactorialEndpoints i:ℕ)/100
   .add (.scale a (.log i.val a)) (.rat (-a))))
   (.scale (-10) (.add (.scale (33/100) (.log 10 (33/100))) (.rat (-(33/100)))))

def gExpr (k : Fin 50000) : Expr :=
 .add
  (.add
   (.add entropyExpr
    (.scale 5 (.add (jExpr k 0 1) (.scale (-1) (jExpr k 1 (-1))))))
   (.scale (-1) (.sum 15 (fun i =>
     .add (jExpr k (alphaSlot i) (alpha i))
       (.scale (-1) (jExpr k (alphaSlot i+1) (-alpha i)))))))
  (.add (.scale ((-2)*right k+19/20000) .pi)
   (.scale (3/50000) (.sum 15 (fun i => .log (slopeSlot i) ((1+alpha i)/(1-alpha i))))))

theorem jExpr_eval (k : Fin 50000) (slot : ℕ) (a : ℚ) :
 (jExpr k slot a).eval = certificateJ (1+(3/5)*(right k:ℝ)+(a:ℝ)) (right k:ℝ) := by
 simp [jExpr,Expr.eval,certificateJ]
 <;> ring

theorem entropyExpr_eval : entropyExpr.eval = targetNormalizationEntropy := by
 simp [entropyExpr,Expr.eval,targetNormalizationEntropy,entropyTerm]
 <;> ring

theorem alpha_cast (i : Fin 15) : (alpha i:ℝ)=targetAlpha i := by
 simp [alpha,targetAlpha]

theorem gExpr_eval (k : Fin 50000) :
 (gExpr k).eval = certificateG (right k:ℝ)-2*Real.pi*(right k:ℝ)+cellSlope*(1/10000) := by
 simp only [gExpr,Expr.eval,entropyExpr_eval,jExpr_eval]
 push_cast
 simp only [alpha_cast]
 unfold certificateG cellSlope
 ring

end OddZeta.FourValue.FullGrid
'''
(p/'FourValueFullGridExpressions.lean').write_text(s)
l=p/'lakefile.toml';t=l.read_text();t=t.replace('roots = [','roots = ["FourValueFullGridExpressions", ');l.write_text(t)

import FourValueRationalBoxes

noncomputable section
namespace OddZeta.FourValue.ArithmeticCertificate
open Finset

def tailA : Fin 10 → ℕ := ![63,60,58,57,54,52,49,47,44,42]
def allA : Fin 12 → ℕ := ![100,67,63,60,58,57,54,52,49,47,44,42]

structure Box where
 lo : ℚ
 hi : ℚ
 plusLo : Fin 12 → ℤ
 plusHi : Fin 12 → ℤ
 minusLo : Fin 12 → ℤ
 minusHi : Fin 12 → ℤ
 cap : ℕ
 lam : ℤ
 nu : ℤ
 good : Bool
 single : Bool
 pen : ℤ

def Box.lowerCount (B : Box) (i : Fin 12) : ℤ := B.plusLo i+B.minusLo i+1
def Box.upperCount (B : Box) (i : Fin 12) : ℤ := B.plusHi i+B.minusHi i+1

def Box.cost (B : Box) (m : ℕ) : ℤ :=
 if B.good then
   if B.single then max ((m:ℤ)^2+B.lam*m) (B.nu*m)
   else (m:ℤ)^2+B.lam*m
 else (m:ℤ)^2+(B.lam-5)*m

structure Box.Valid (B : Box) (l h : ℚ) (price norm : ℤ) : Prop where
 lt : B.lo<B.hi
 lower : 0≤B.lo
 upper : B.hi≤h/2
 floors : ∀ i,∀ u∈({l,h}:Finset ℚ),∀ y∈({B.lo,B.hi}:Finset ℚ),
   (B.plusLo i:ℚ)*u≤allA i+y ∧ allA i+y≤(B.plusHi i+1:ℚ)*u ∧
   (B.minusLo i:ℚ)*u≤allA i-y ∧ allA i-y≤(B.minusHi i+1:ℚ)*u
 capacity : (∑i : Fin 10,B.upperCount ⟨i.val+2,by omega⟩)≤B.cap
 lambda : B.lam≤norm+5*B.lowerCount 0-5*B.upperCount 1-
   ∑i : Fin 10,B.upperCount ⟨i.val+2,by omega⟩
 normalization : B.nu≤norm
 good_corners : B.good=true → ∀u∈({l,h}:Finset ℚ),∀y∈({B.lo,B.hi}:Finset ℚ),
   67-y+u*(B.plusHi 2:ℚ)≤u ∧ 67+y+u*(B.minusHi 2:ℚ)≤u
 single_count : B.single=true → B.plusHi 2+B.minusHi 2≤0
 penalty_nonneg : 0≤B.pen
 dual : ∀m : Fin (B.cap+1),price*(m.val:ℤ)-B.pen≤B.cost m.val

structure Cell where
 lo : ℚ
 hi : ℚ
 price : ℤ
 normFloors : Fin 10 → ℤ
 norm33 : ℤ
 count : ℕ
 cut : Fin (count+1) → ℚ
 box : Fin count → Box
 k : ℕ
 lower : ℚ

def Cell.norm (c : Cell) : ℤ := ∑i,c.normFloors i-10*c.norm33
def Cell.widthPenalty (c : Cell) : ℚ := ∑i,((c.box i).hi-(c.box i).lo)*(c.box i).pen

structure Cell.Valid (c : Cell) : Prop where
 lo_pos : 1/20≤c.lo
 lt : c.lo<c.hi
 hi_le : c.hi≤361
 price_abs : |c.price|≤20000
 normalization : ∀i,0≤c.normFloors i ∧ (c.normFloors i:ℚ)*c.hi≤2*tailA i
 norm33_pos : 0<c.norm33+1
 norm33_bound : 33≤(c.norm33+1:ℚ)*c.lo
 cut_zero : c.cut 0=0
 cut_last : c.cut (Fin.last c.count)=c.hi/2
 cut_mono : StrictMono c.cut
 boxes : ∀i,(c.box i).lo=c.cut i.castSucc ∧ (c.box i).hi=c.cut i.succ ∧
   (c.box i).Valid c.lo c.hi c.price c.norm
 k_bounds : c.lo*c.k≤361 ∧ 361≤c.lo*(c.k+1)
 lower_bound : c.lower≤c.price*(361/2)-c.widthPenalty-
   (361*c.k-c.lo*c.k*(c.k+1)/2)
end OddZeta.FourValue.ArithmeticCertificate

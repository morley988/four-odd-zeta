import FourValueTranscendentalInterval

namespace OddZeta.FourValue.Fast
open OddZeta.FourValue.Transcendental

/-- Numerator endpoints at one fixed positive scale. -/
structure Interval where
  lo : ℤ
  hi : ℤ
  deriving Repr, DecidableEq

namespace Interval
noncomputable def Contains (S : ℕ) (a : Interval) (x : ℝ) : Prop :=
  (a.lo:ℝ) ≤ (S:ℝ)*x ∧ (S:ℝ)*x ≤ (a.hi:ℝ)

def zero : Interval := ⟨0,0⟩
def add (a b : Interval) : Interval := ⟨a.lo+b.lo,a.hi+b.hi⟩
def neg (a : Interval) : Interval := ⟨-a.hi,-a.lo⟩
def divNat (d : ℕ) (a : Interval) : Interval := ⟨a.lo/d,-((-a.hi)/d)⟩
def mul (S : ℕ) (a b : Interval) : Interval :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))/S,
   -((-max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi)))/S)⟩
def ofRat (S : ℕ) (q : ℚ) : Interval := ⟨⌊(S:ℚ)*q⌋,⌈(S:ℚ)*q⌉⟩

theorem quotient_bounds (v : ℤ) (d : ℕ) :
    ((v/(d:ℤ):ℤ):ℝ) ≤ (v:ℝ)/(d:ℝ) ∧
    (v:ℝ)/(d:ℝ) ≤ ((-((-v)/(d:ℤ)):ℤ):ℝ) := by
  have hl := Int.floor_le ((v:ℚ)/(d:ℚ))
  have hu := Int.le_ceil ((v:ℚ)/(d:ℚ))
  rw [Rat.floor_intCast_div_natCast] at hl
  rw [Rat.ceil_intCast_div_natCast] at hu
  constructor
  · exact_mod_cast hl
  · exact_mod_cast hu

theorem zero_contains (S : ℕ) : Contains S zero 0 := by simp [Contains,zero]

theorem add_contains {S : ℕ} {a b : Interval} {x y : ℝ}
    (ha : Contains S a x) (hb : Contains S b y) : Contains S (a.add b) (x+y) := by
  dsimp [Contains,add] at *
  push_cast
  constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]

theorem neg_contains {S : ℕ} {a : Interval} {x : ℝ}
    (ha : Contains S a x) : Contains S a.neg (-x) := by
  dsimp [Contains,neg] at *
  push_cast
  constructor <;> linarith [ha.1,ha.2]

theorem divNat_contains {S : ℕ} (d : ℕ) (hd : 0 < d) {a : Interval} {x : ℝ}
    (ha : Contains S a x) : Contains S (a.divNat d) (x/(d:ℝ)) := by
  have hd' : (0:ℝ) ≤ d := by positivity
  have hl := (quotient_bounds a.lo d).1.trans (div_le_div_of_nonneg_right ha.1 hd')
  have hu := (div_le_div_of_nonneg_right ha.2 hd').trans (quotient_bounds a.hi d).2
  simpa [Contains,divNat,mul_div_assoc] using And.intro hl hu

theorem ofRat_contains (S : ℕ) (q : ℚ) : Contains S (ofRat S q) (q:ℝ) := by
  have hl := Int.floor_le ((S:ℚ)*q)
  have hu := Int.le_ceil ((S:ℚ)*q)
  constructor
  · exact_mod_cast hl
  · exact_mod_cast hu

theorem mul_contains (S : ℕ) (hS : 0 < S) {a b : Interval} {x y : ℝ}
    (ha : Contains S a x) (hb : Contains S b y) : Contains S (a.mul S b) (x*y) := by
  have h1 := QInterval.scalar_bounds (a.lo:ℝ) b.lo b.hi ((S:ℝ)*y) hb
  have h2 := QInterval.scalar_bounds (a.hi:ℝ) b.lo b.hi ((S:ℝ)*y) hb
  have h3 := QInterval.scalar_bounds ((S:ℝ)*y) a.lo a.hi ((S:ℝ)*x) ha
  simp only [mul_comm ((S:ℝ)*y)] at h3
  have h := And.intro ((min_le_min h1.1 h2.1).trans h3.1)
    (h3.2.trans (max_le_max h1.2 h2.2))
  let l := min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))
  let u := max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))
  have hl : (l:ℝ) ≤ ((S:ℝ)*x)*((S:ℝ)*y) := by simpa [l,or_assoc] using h.1
  have hu : ((S:ℝ)*x)*((S:ℝ)*y) ≤ (u:ℝ) := by simpa [u,or_assoc] using h.2
  have hS' : (0:ℝ) < S := by exact_mod_cast hS
  have he : ((S:ℝ)*x)*((S:ℝ)*y)/(S:ℝ) = (S:ℝ)*(x*y) := by field_simp
  have hlo := (quotient_bounds l S).1.trans (div_le_div_of_nonneg_right hl hS'.le)
  have hhi := (div_le_div_of_nonneg_right hu hS'.le).trans (quotient_bounds u S).2
  rw [he] at hlo hhi
  exact ⟨hlo,hhi⟩

def mulFast (S : ℕ) (a b : Interval) : Interval :=
  if 0 ≤ a.lo ∧ 0 ≤ b.lo then
    ⟨(a.lo*b.lo)/S,-((-(a.hi*b.hi))/S)⟩
  else a.mul S b

theorem mulFast_contains (S : ℕ) (hS : 0 < S) {a b : Interval} {x y : ℝ}
    (ha : Contains S a x) (hb : Contains S b y) : Contains S (a.mulFast S b) (x*y) := by
  dsimp [mulFast]
  split_ifs with hp
  · have ha0 : (0:ℝ) ≤ a.lo := by exact_mod_cast hp.1
    have hb0 : (0:ℝ) ≤ b.lo := by exact_mod_cast hp.2
    have hS' : (0:ℝ) < S := by exact_mod_cast hS
    have hl := mul_le_mul ha.1 hb.1 hb0 (ha0.trans ha.1)
    have hu := mul_le_mul ha.2 hb.2 (hb0.trans hb.1) (ha0.trans (ha.1.trans ha.2))
    have hlo := (quotient_bounds (a.lo*b.lo) S).1
    have hhi := (quotient_bounds (a.hi*b.hi) S).2
    push_cast at hlo hhi
    have he : ((S:ℝ)*x)*((S:ℝ)*y)/(S:ℝ) = (S:ℝ)*(x*y) := by field_simp
    exact ⟨by simpa only [he,Int.cast_neg] using hlo.trans (div_le_div_of_nonneg_right hl hS'.le),
      by simpa only [he,Int.cast_neg] using (div_le_div_of_nonneg_right hu hS'.le).trans hhi⟩
  · exact mul_contains S hS ha hb

def toQ (S : ℕ) (a : Interval) : QInterval := ⟨(a.lo:ℚ)/S,(a.hi:ℚ)/S⟩

theorem toQ_contains (S : ℕ) (hS : 0 < S) {a : Interval} {x : ℝ}
    (ha : Contains S a x) : (a.toQ S).Contains x := by
  have hS' : (0:ℝ) < S := by exact_mod_cast hS
  dsimp [toQ,QInterval.Contains]
  push_cast
  constructor
  · apply (div_le_iff₀ hS').mpr
    simpa only [mul_comm x] using ha.1
  · apply (le_div_iff₀ hS').mpr
    simpa only [mul_comm x] using ha.2

/-- No rational normalization takes place inside this recurrence. -/
def seriesState (S : ℕ) (alternating : Bool) (X X2 : Interval) : ℕ → Interval × Interval
  | 0 => (X, zero)
  | n+1 =>
    let st := seriesState S alternating X X2 n
    let term := st.1.divNat (2*n+1)
    let term := if alternating && n%2==1 then term.neg else term
    (st.1.mulFast S X2, st.2.add term)

def series (S n : ℕ) (alternating : Bool) (q : ℚ) : Interval :=
  let X := ofRat S q
  (seriesState S alternating X (X.mulFast S X) n).2

noncomputable def signedTerm (alternating : Bool) (n : ℕ) (x : ℝ) : ℝ :=
  if alternating && n%2==1 then -(x^(2*n+1)/(2*n+1)) else x^(2*n+1)/(2*n+1)

theorem seriesState_contains (S : ℕ) (hS : 0 < S) (alternating : Bool)
    (X X2 : Interval) (x : ℝ) (hx : Contains S X x) (hx2 : Contains S X2 (x^2)) (n : ℕ) :
    Contains S (seriesState S alternating X X2 n).1 (x^(2*n+1)) ∧
    Contains S (seriesState S alternating X X2 n).2 (∑ j ∈ Finset.range n, signedTerm alternating j x) := by
  induction n with
  | zero => simpa [seriesState] using And.intro hx (zero_contains S)
  | succ n ih =>
    have hp := mulFast_contains S hS ih.1 hx2
    have ht := divNat_contains (2*n+1) (by omega) ih.1
    norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at ht
    have hs : Contains S
        (if alternating && n%2==1 then ((seriesState S alternating X X2 n).1.divNat (2*n+1)).neg
          else (seriesState S alternating X X2 n).1.divNat (2*n+1)) (signedTerm alternating n x) := by
      dsimp [signedTerm]
      split_ifs
      · exact neg_contains ht
      · exact ht
    constructor
    · convert hp using 1
      congr 1
      rw [← pow_add]
      congr 1
    · simpa only [seriesState,Finset.sum_range_succ] using add_contains ih.2 hs

theorem series_contains (S n : ℕ) (hS : 0 < S) (alternating : Bool) (q : ℚ) :
    Contains S (series S n alternating q) (∑ j ∈ Finset.range n, signedTerm alternating j (q:ℝ)) := by
  have hq := ofRat_contains S q
  exact (seriesState_contains S hS alternating _ _ _ hq
    (by simpa [pow_two] using mulFast_contains S hS hq hq) n).2

theorem log_series_contains (S n : ℕ) (hS : 0 < S) (q : ℚ) :
    Contains S (series S n false q) (∑ j ∈ Finset.range n, (q:ℝ)^(2*j+1)/(2*j+1)) := by
  simpa [signedTerm] using series_contains S n hS false q

theorem atan_series_contains (S n : ℕ) (hS : 0 < S) (q : ℚ) :
    Contains S (series S n true q) (Transcendental.atanPoly n (q:ℝ)) := by
  have h := series_contains S n hS true q
  have he : (∑ j ∈ Finset.range n, signedTerm true j (q:ℝ)) = Transcendental.atanPoly n (q:ℝ) := by
    apply Finset.sum_congr rfl
    intro j _
    dsimp [signedTerm]
    rw [neg_one_pow_eq_pow_mod_two]
    have hj : j%2=0 ∨ j%2=1 := by omega
    rcases hj with hj | hj <;> simp [hj,neg_div]
  rwa [he] at h

def horner (S : ℕ) (alternating : Bool) (X2 : Interval) (j : ℕ) : ℕ → Interval
  | 0 => zero
  | n+1 =>
    let c := (Interval.mk (S:ℤ) (S:ℤ)).divNat (2*j+1)
    let c := if alternating && j%2==1 then c.neg else c
    c.add (X2.mulFast S (horner S alternating X2 (j+1) n))

def hornerSeries (S n : ℕ) (alternating : Bool) (q : ℚ) : Interval :=
  let X := ofRat S q
  X.mulFast S (horner S alternating (X.mulFast S X) 0 n)

noncomputable def signedCoeff (alternating : Bool) (j : ℕ) : ℝ :=
  if alternating && j%2==1 then -(1/(2*j+1)) else 1/(2*j+1)

noncomputable def hornerPoly (alternating : Bool) (x : ℝ) (j : ℕ) : ℕ → ℝ
  | 0 => 0
  | n+1 => signedCoeff alternating j + x^2 * hornerPoly alternating x (j+1) n

theorem horner_contains (S : ℕ) (hS : 0 < S) (alternating : Bool)
    (X2 : Interval) (x : ℝ) (hx2 : Contains S X2 (x^2)) (j n : ℕ) :
    Contains S (horner S alternating X2 j n) (hornerPoly alternating x j n) := by
  induction n generalizing j with
  | zero => exact zero_contains S
  | succ n ih =>
    have hc0 : Contains S (Interval.mk (S:ℤ) (S:ℤ)) 1 := by simp [Contains]
    have hc := divNat_contains (2*j+1) (by omega) hc0
    norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hc
    have hc' : Contains S
        (if alternating && j%2==1 then ((Interval.mk (S:ℤ) (S:ℤ)).divNat (2*j+1)).neg
          else (Interval.mk (S:ℤ) (S:ℤ)).divNat (2*j+1)) (signedCoeff alternating j) := by
      dsimp [signedCoeff]
      split_ifs
      · exact neg_contains hc
      · exact hc
    exact add_contains hc' (mulFast_contains S hS hx2 (ih (j+1)))

theorem hornerPoly_sum (alternating : Bool) (x : ℝ) (j n : ℕ) :
    x^(2*j+1)*hornerPoly alternating x j n =
      ∑ k ∈ Finset.range n, signedTerm alternating (j+k) x := by
  induction n generalizing j with
  | zero => simp [hornerPoly]
  | succ n ih =>
    rw [hornerPoly, Finset.sum_range_succ']
    have hp : x^(2*j+1)*x^2=x^(2*(j+1)+1) := by rw [← pow_add]; congr 1
    rw [mul_add, ← mul_assoc, hp, ih]
    have he : x^(2*j+1)*signedCoeff alternating j=signedTerm alternating j x := by
      dsimp [signedCoeff,signedTerm]
      split_ifs <;> ring
    rw [he]
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
    ring

theorem hornerSeries_contains (S n : ℕ) (hS : 0 < S) (alternating : Bool) (q : ℚ) :
    Contains S (hornerSeries S n alternating q) (∑ j ∈ Finset.range n, signedTerm alternating j (q:ℝ)) := by
  have hx := ofRat_contains S q
  have hx2 : Contains S ((ofRat S q).mulFast S (ofRat S q)) ((q:ℝ)^2) := by
    simpa [pow_two] using mulFast_contains S hS hx hx
  have h := mulFast_contains S hS hx (horner_contains S hS alternating _ _ hx2 0 n)
  have he := hornerPoly_sum alternating (q:ℝ) 0 n
  simpa [hornerSeries,show (q:ℝ)*hornerPoly alternating (q:ℝ) 0 n =
      ∑ j ∈ Finset.range n, signedTerm alternating j (q:ℝ) by simpa using he] using h

theorem log_horner_contains (S n : ℕ) (hS : 0 < S) (q : ℚ) :
    Contains S (hornerSeries S n false q) (∑ j ∈ Finset.range n, (q:ℝ)^(2*j+1)/(2*j+1)) := by
  simpa [signedTerm] using hornerSeries_contains S n hS false q

theorem atan_horner_contains (S n : ℕ) (hS : 0 < S) (q : ℚ) :
    Contains S (hornerSeries S n true q) (Transcendental.atanPoly n (q:ℝ)) := by
  have h := hornerSeries_contains S n hS true q
  have he : (∑ j ∈ Finset.range n, signedTerm true j (q:ℝ)) = Transcendental.atanPoly n (q:ℝ) := by
    apply Finset.sum_congr rfl
    intro j _
    dsimp [signedTerm]
    rw [neg_one_pow_eq_pow_mod_two]
    have hj : j%2=0 ∨ j%2=1 := by omega
    rcases hj with hj | hj <;> simp [hj,neg_div]
  rwa [he] at h

end Interval
end OddZeta.FourValue.Fast

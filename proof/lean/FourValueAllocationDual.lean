import FourValuePadicMinors

noncomputable section
namespace OddZeta.FourValue.Allocation
open Finset

/-- The integer marginal cost of adding one dimension. -/
def marginal (cost : ℕ → ℤ) (j : ℕ) : ℤ := cost (j+1)-cost j

/-- A finite dual penalty. Convexity is not required for this lower bound. -/
def penalty (cap : ℕ) (cost : ℕ → ℤ) (price : ℤ) : ℤ :=
 ∑ j ∈ range cap, max 0 (price-marginal cost j)

theorem penalty_nonneg (cap : ℕ) (cost : ℕ → ℤ) (price : ℤ) :
 0 ≤ penalty cap cost price := by
 apply sum_nonneg
 intro j hj
 exact le_max_left _ _

theorem prefix_cost (cost : ℕ → ℤ) (hzero : cost 0=0) (m : ℕ) :
 (∑ j ∈ range m, marginal cost j)=cost m := by
 simpa [marginal,hzero] using sum_range_sub cost m

theorem cost_dual_lower (cap m : ℕ) (cost : ℕ → ℤ) (price : ℤ)
 (hzero : cost 0=0) (hm : m≤cap) :
 price*(m:ℤ)-penalty cap cost price ≤ cost m := by
 have hterm : ∀ j, price-max 0 (price-marginal cost j) ≤ marginal cost j := by
   intro j
   have := le_max_right (0:ℤ) (price-marginal cost j)
   linarith
 have hsum := sum_le_sum (s:=range m) (fun j _ => hterm j)
 rw [sum_sub_distrib,prefix_cost cost hzero] at hsum
 simp only [sum_const,card_range,nsmul_eq_mul] at hsum
 have hpen : (∑ j ∈ range m,max 0 (price-marginal cost j)) ≤ penalty cap cost price := by
   apply sum_le_sum_of_subset_of_nonneg (range_mono hm)
   intro j hj hnot
   exact le_max_left _ _
 nlinarith

/-- A lower bound for every feasible discrete allocation, not an assumed optimizer. -/
theorem allocation_dual_lower {ι : Type*} [Fintype ι]
 (cap mass : ι → ℕ) (cost : ι → ℕ → ℤ) (price : ℤ) (K : ℕ)
 (hzero : ∀ i,cost i 0=0) (hcap : ∀ i,mass i≤cap i)
 (hmass : ∑ i,mass i=K) :
 price*(K:ℤ)-(∑ i,penalty (cap i) (cost i) price) ≤ ∑ i,cost i (mass i) := by
 have h := sum_le_sum (s:=univ) (fun i _ => cost_dual_lower (cap i) (mass i) (cost i) price (hzero i) (hcap i))
 rw [sum_sub_distrib,← mul_sum] at h
 simpa only [← Nat.cast_sum,hmass] using h

/-- Multiplicity-weighted dual certificate, used by the continuous partition. -/
theorem weighted_dual_lower {ι : Type*} [Fintype ι]
 (width : ι → ℝ) (cost mass penalties : ι → ℝ) (price C : ℝ)
 (hw : ∀ i,0≤width i) (hcost : ∀ i,price*mass i-penalties i≤cost i)
 (hmass : ∑ i,width i*mass i=C) :
 price*C-(∑ i,width i*penalties i) ≤ ∑ i,width i*cost i := by
 have h := sum_le_sum (s:=univ) (fun i _ => mul_le_mul_of_nonneg_left (hcost i) (hw i))
 simp_rw [mul_sub,mul_left_comm (width _) price] at h
 rw [sum_sub_distrib,← mul_sum,hmass] at h
 exact h

/-- Polynomial costs of a bad or good noncentral residue class. -/
def quadraticCost (lambda : ℤ) (m : ℕ) : ℤ := (m:ℤ)^2+lambda*m

def singleCost (lambda nu : ℤ) (m : ℕ) : ℤ := max (quadraticCost lambda m) (nu*m)

theorem quadraticCost_zero (lambda : ℤ) : quadraticCost lambda 0=0 := by simp [quadraticCost]
theorem singleCost_zero (lambda nu : ℤ) : singleCost lambda nu 0=0 := by simp [singleCost,quadraticCost]
theorem quadratic_marginal (lambda : ℤ) (m : ℕ) :
 marginal (quadraticCost lambda) m=2*(m:ℤ)+1+lambda := by
 simp [marginal,quadraticCost]; ring

end OddZeta.FourValue.Allocation

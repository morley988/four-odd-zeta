import FourValueLaurentObservations

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem finiteHarmonic_succ (m s : ℕ) :
    finiteHarmonic (K:=K) (m+1) s=finiteHarmonic m s+1/((m+1:ℕ):K)^s := by
  simp [finiteHarmonic,Finset.sum_range_succ]

theorem finiteHarmonic_boundary (b : ℕ) (j : ℤ) (hj : j<(b:ℤ)) (s : ℕ) :
    finiteHarmonic (K:=K) ((b-j).toNat) s - finiteHarmonic ((b-(j+1)).toNat) s =
      1/((b:K)-(j:K))^s := by
  have hn : (b-j).toNat=(b-(j+1)).toNat+1 := by omega
  rw [hn,finiteHarmonic_succ,add_sub_cancel_left]
  have hc : (((b-(j+1)).toNat+1:ℕ):K)=(b:K)-(j:K) := by
    have ht : (((b-(j+1)).toNat+1:ℕ):ℤ)=(b:ℤ)-j := by omega
    exact_mod_cast ht
  rw [hc]

end OddZeta.FourValue

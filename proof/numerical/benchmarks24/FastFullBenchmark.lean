import FourValueFastEvaluator
open OddZeta.FourValue.Fast
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true in
example : ∀ k : Fin 100,
    (logInterval (2^80) 24 16 (((k:ℚ)+1)/37)).any
      (fun a => decide (a.lo ≤ a.hi ∧ a.hi-a.lo ≤ (1/10^18:ℚ))) = true := by decide +kernel
set_option profiler true in
example : ∀ k : Fin 100,
    let a := atanInterval (2^80) 32
      ⟨314159265358979323844/10^20,314159265358979323864/10^20⟩ (((k:ℚ)-50)/13)
    a.lo ≤ a.hi ∧ a.hi-a.lo ≤ (1/10^18:ℚ) := by decide +kernel

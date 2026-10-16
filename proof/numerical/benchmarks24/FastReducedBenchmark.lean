import FourValueFastReduction
open OddZeta.FourValue.Fast
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true in
example : ∀ k : Fin 100,
    (reducedLogInterval (2^80) 24 64 ((((k:ℚ)+1)^2)/10^8)).any
      (fun a => decide (a.lo ≤ a.hi ∧ a.hi-a.lo ≤ (1/10^18:ℚ))) = true := by decide +kernel

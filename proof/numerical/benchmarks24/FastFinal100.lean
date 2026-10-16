import FourValueFastInterval
open OddZeta.FourValue.Fast Interval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true in
example : ∀ k : Fin 100, (hornerSeries (2^80) 24 false ((k:ℚ)/300)).lo ≥ 0 := by decide +kernel

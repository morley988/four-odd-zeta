import FourValueTranscendentalInterval
open OddZeta.FourValue.Transcendental QInterval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true in
example : ∀ k : Fin 100, (series (2^80) 24 (fun j => 1/(2*j+1)) ((k:ℚ)/300)).lo ≥ 0 := by decide +kernel

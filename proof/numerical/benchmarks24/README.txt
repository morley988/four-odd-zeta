ROUND 24 KERNEL BENCHMARKS

Current final tests, after building the main project:
  cd lean
  lake env lean ../numerical/benchmarks24/FastFinal100.lean
  lake env lean ../numerical/benchmarks24/FastHornerBenchmark.lean
  lake env lean ../numerical/benchmarks24/FastFinalFull1000.lean
  lake env lean ../numerical/benchmarks24/FastReducedBenchmark.lean

All use decide +kernel, not native evaluation. maxHeartbeats=0 removes the
elaborator heartbeat cutoff, not any proof obligation or kernel check.
FastFinal100 checks 100 series lower endpoints; FastFinalFull1000 checks
ordered endpoints and width <= 1e-18 for 1000 logs and 1000 arctangents.
The full numerical certificate is not one of these tests.

Historical versions/timings:
- Round23 baseline: ../IntervalBenchmark.lean, using the unchanged
  FourValueTranscendentalInterval module; 66.7 seconds from prior round.
- integer100 / integer1000: integer_v1.lean snapshots the initial general
  multiplication backend. Input counts 100 (denominator 300) and 1000
  (denominator 3000). Its recurrence is named Interval.series.
- positive1000: current Interval.series with mulFast, input count 1000.
- horner1000 / final100: current Interval.hornerSeries, respectively 1000
  and 100 inputs, denominator respectively 3000 and 300.
- full100_v2: evaluator_power.lean snapshots the both-power evaluator.
- horner_full100: both-Horner evaluator, same inputs as FastFullBenchmark.
- current final frontend: Horner for log and power recurrence for atan.
- small_recursive100: FastSmallBenchmark, log arguments (k+1)^2/10^8.
- small_reduced100: FastReducedBenchmark, same arguments, accumulated exponent.

The first full100.log contains a Decidable-instance elaboration failure in
the original proposition-valued Option match. The Option.any Boolean form
in the revised harness passed; this was not a numeric counterexample.
Historical test files run against CURRENT imported modules will measure
current code, not the archived snapshots. Do not treat those as bit-identical
reproductions of historical timing without restoring the stated variant.

JSON files record subprocess wall/CPU time, max RSS in KiB and exit codes.
Profiler logs isolate kernel type-checking time from startup/import overhead.
run_benchmark.py records the workspace-specific invocation used this round;
the portable lake commands above are preferred elsewhere.

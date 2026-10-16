Round 25 end-to-end certificate batch

The production batch covers actual grid cells 0, 5669, and 49999 (width 1/10000),
all 45 basis centers and all 42 knots. Generated Lean sources are in ../../lean.
FourValueBatchTools proves general soundness; FourValueBatch.selected_cells_bound
is the combined whole-cell theorem. No external numerical assumption is used
in these three cells. This is not the full 50,000-cell certificate.

Reproduction with pinned Lean/mathlib restored:
  cd <archive project root>
  export FOUR_VALUE_PROJECT="$PWD"
  python3 numerical/batch25/generate.py 0
  python3 numerical/batch25/generate.py 5669
  python3 numerical/batch25/generate.py 49999
  python3 numerical/batch25/patch_cells.py
  (cd lean && bash verify.sh)
Generators require numpy and python-flint. Arb generates candidate endpoints;
Lean's kernel checks them against the proved interval evaluators. The build
itself needs no Python numerical library and uses the committed Lean sources.

After the build, measure cells sequentially with:
  python3 numerical/batch25/run_batch.py 0
  python3 numerical/batch25/run_batch.py 5669
  python3 numerical/batch25/run_batch.py 49999
The harness uses normal lake in the archive. In the original sandbox it used
a run_lean.sh compatibility wrapper for the same pinned executable.

Only timing0.json, timing5669.json, timing49999.json and matching *.timed.log
files describe the final successful benchmark. Times include imports, scalar
proof elaboration, kernel checking, and assembly, but exclude shared-tool build,
witness generation, combined theorem, and cumulative audit. They are single-run
measurements; no claim of statistical representativeness is made. Peak RSS is
the child-process high-water mark across each cell's two module compilations.
Lean profiler categories overlap and must not be added as elapsed CPU time.

Other logs and Batch*.lean diagnostic sources document development attempts,
including aborted slow table-expansion/cast-unification attempts and corrected
cast elaboration errors. They are not production proof modules and are excluded
from the cumulative axiom audit. Their imports may no longer expose unused
scalar lemmas from earlier generated versions. They are retained for diagnosis,
not presented as successful proofs. Files under ../../lean are authoritative.

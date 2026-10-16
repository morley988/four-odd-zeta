FOUR-VALUE LEAN PROOF — ROUND 25
End-to-end certificate batch

RESULT
The requested batch milestone is complete. Three actual cells of the 50,000-cell
certificate are kernel-verified from concrete numerical witnesses through the
whole-cell real inequality, for every one of the 42 knots:
  k = 0:     [0, 0.0001], with y > 0;
  k = 5669:  [0.5669, 0.5670];
  k = 49999: [4.9999, 5].
Cell 5669 attains the stored final-knot grid bound; the other two exercise the
small-height endpoint and the boundary with the infinite-tail argument.
This is 3/50,000 cells, not a full numerical certificate or the final irrationality
theorem. No full-grid numerical assumption appears in these three cell proofs.

FORMAL STATEMENT
OddZeta.FourValue.Batch.selected_cells_bound takes k in [0,5669,49999], m <= 41,
y > 0, k/10000 <= y <= (k+1)/10000, and proves
  certificateG y - 2*pi*y
    + basisKnot m * analyticBasisPotential (basisKnotWeight m)
        ((normalizedContourPoint y)^2)
  <= Numerical.height m.
The combined theorem applies the three concrete CellCertificate instances and
the proved general cell_certificate_sound theorem. The saved key_statements.txt
contains Lean's exact type. All 126 cell/knot combinations hold throughout their
respective intervals, not merely at finitely sampled heights.

WHAT LEAN CHECKS
For each cell, 46 logarithm and 24 arctangent scalar enclosures establish the
stored G ceiling, including entropy normalization and the cell slope allowance.
All 45 centers have exact rational squared-distance checks at both endpoints,
for the center and its complex conjugate: 180 endpoint checks per cell. The
square-root ceiling candidates are nonnegative and at least 1/50.
A further 90 logarithm evaluations establish the 45 stored K ceilings, including
the 17/5,000,000,000 curvature allowance. Exact rational checks then establish
all 42 weighted knot inequalities against the committed height table.
The general interpolation lemmas propagate those bounds across the whole cell.

Arb at 256-bit precision generates scalar endpoint candidates; rational integer
square roots generate distance candidates. These external computations are not
trusted proof steps. Every candidate and finite inequality is checked by Lean,
using the formally sound integer interval evaluator and decide +kernel. The
interval scale is 2^80, logarithm series length 24, arctangent length 32, and
logarithm reduction fuel 64. The verified Machin enclosure supplies pi.
The G/K integers come from the existing Round 7 replay arrays. Centers, knot
weights, and target heights come from the already committed Lean tables.

MEASURED PERFORMANCE (SEQUENTIAL CELL BUILDS)
Cell     0: 46.00 s wall; 49.40 s CPU; 5.04 GiB peak RSS
Cell  5669: 54.20 s wall; 57.05 s CPU; 5.02 GiB peak RSS
Cell 49999: 53.29 s wall; 56.71 s CPU; 5.04 GiB peak RSS
Total: 153.49 seconds wall, 163.16 seconds CPU; peak 5.04 GiB.
These are single-run end-to-end module compilations, including imports, proof
elaboration, kernel checking and assembly. Shared-tool compilation, witness
generation, final combined theorem and cumulative audit are excluded. See the
JSON and logs in numerical/batch25. Lean profiler categories overlap and are
not independent elapsed times.

The batch exposed costs missed by the earlier evaluator-only benchmark. Naively
repeating this per-cell layout over 50,000 cells gives about
711 single-worker wall-hours (29.6 days), or
755 CPU-hours. This is a mechanical extrapolation from only three
selected cells, not a validated forecast. It includes repeated imports and
scalar-proof assembly that larger batches could share. The earlier 1–3 day
whole-stage estimate is not supported by the current per-cell implementation.
The fast evaluator alone is insufficient to estimate full-certificate runtime.

Before a full-grid run, the useful next work is shared constant enclosures,
integer/sparse weighted-knot checks, and batched assembly with controlled memory.
The full grid may also contain harder precision or ceiling cases not exercised
here. No additional precision was needed for this three-cell batch.

IMPLEMENTATION FINDINGS
Direct expansion of complex-distance and weight tables was replaced by finite
rational checks and reusable soundness lemmas. K bounds now check logarithm
pairs directly, avoiding redundant separately elaborated scalar lemmas.
Some assembly attempts stalled while reconciling rational-to-real casts and
nonzero cell-width expressions; explicit cast normalization and a proved width
identity resolved those issues. One intermediate second-cell process ended
without a timing receipt; the final complete successful rerun is authoritative.
Aborted/failed diagnostic logs are retained and clearly excluded from success
claims. Final generated sources reproduce from the saved witness generator.

AUDIT AND PRESERVATION
254 new theorem declarations in 8 modules.
1669 cumulative audited declarations in 229 substantive modules.
The full Lake build and every-declaration axiom audit passed. Only propext,
Classical.choice and Quot.sound are allowed. No sorry, admit, native_decide or
custom axiom occurs. All 221 Round 24 substantive Lean modules are byte-for-byte
unchanged. Exact source hashes and audit outputs are included.
Lean: leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474
Checkpoint: 2026-10-14T23:08:04.548650+00:00

REMAINING OBLIGATIONS
The full GridCertificate 50000 is still uninstantiated. The other 49,997 cells
must be certified and assembled before applying finite_certificate_of_grid.
The global arithmetic lower bound and final contradiction also remain.
No unconditional irrationality theorem for zeta(7), zeta(9), zeta(11), zeta(13)
is claimed. No process is left running after this checkpoint.

REPRODUCTION
Restore the pinned Lean/mathlib dependencies and run lean/verify.sh. Committed
Lean sources suffice for verification. Optional witness regeneration and timing
commands are in numerical/batch25/README.txt. The archive is cumulative; runtime
binaries and .lake caches are excluded. See SHA256_MANIFEST.txt for file hashes.

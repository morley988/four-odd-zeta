FOUR-VALUE ZETA PROJECT — ROUND 27
Full-grid linkage and remaining calculation interfaces: COMPLETE

STATUS
The full 50,000-cell grid certificate is assembled in Lean. It yields the
finite knot certificate, the whole positive contour (including the already
proved infinite tail), the interpolated envelope, and the numerical determinant
rate with no remaining numerical-certificate hypothesis.

The result is conditional on seven explicitly marked external calculation
families. It is not a fully kernel-certified numerical proof, and the full
four-value irrationality theorem is not yet completed.

FINAL ANALYTIC OUTPUT
OddZeta.FourValue.FullGrid.numerical_rate proves the existence of E(n) with
E(n)/n^2 tending to zero, such that all required matrix minors satisfy
  |det M_n[rows,cols]| <= exp((100 n)^2 * (-577853339/50000000) + E(n)).
The numerical rate is -11.55706678. Interpolation, the infinite tail,
asymptotic errors, and the transfer to the determinant bound remain Lean proofs.

VERIFICATION RESULTS
- 50,000 cells of width 1/10,000, covering 0 < y <= 5.
- 42 knots per cell; 2,100,000 exact weighted knot checks.
- 2,400,022 distinct argument identities: 22 shared constants and 48 per cell.
  Repeated uses of those rows in the expression are covered by the same checks.
- 50,000 exact rational G-expression interval upper bounds.
- 9,000,000 exact rational squared endpoint-distance checks.
- 4,500,000 exact rational distance cutoff checks.
- 2,250,000 exact rational logarithm-pair upper-endpoint sums.
- 6,900,022 scalar transcendental intervals rechecked with 256-bit Arb.
- Five deliberately corrupted inputs rejected beyond the hash guard:
  false G upper bound, false knot bound, false log-pair bound,
  wrong logarithm argument, and false distance radius.

Exact rational checking: 127.674 seconds.
Arb checking: 34.280 seconds.
These are observed machine runtimes, not estimates of development time.
The minimum knot slack is exactly zero; exact rational arithmetic verifies the
attained equality, rather than relying on a floating-point tolerance.

ASSUMPTION BOUNDARY: EXACTLY SEVEN ADMITTED BLOCKS
Two unchanged blocks in lean/FourValueExternalTranscendental.lean:
  sorry -- EXTERNAL_TRANSCENDENTAL_VALUE_CERTIFICATION_V1
They assert only the finite table's 5,700,022 logarithm and 1,200,000 arctangent
ranges. This file still contains only these two admitted transcendental claims.

Five blocks in lean/FourValueExternalArithmetic.lean:
  sorry -- EXTERNAL_FINITE_RATIONAL_CERTIFICATION_V1
1. expression_rows: finite rational row identities and row-index bounds.
2. expression_upper: rational interval upper endpoints <= the stored G bounds.
3. distances: rational squared distances and cutoffs for each cell and center.
4. pair_upper: sums of rational log upper endpoints <= the stored K bounds.
5. knot_arithmetic: rational weighted knot inequalities.
All five statements have finite domains and exclusively rational calculation
content. They do not assume analytic inequalities, interpolation, nonvanishing,
the full grid certificate, or the final irrationality theorem.

The full source audit strips comments and strings, checks every Lean source for
unapproved admission tokens, and pins the exact admitted statement files.
The kernel axiom audit covers 1,715 declarations. The 1,669 original theorem
declarations remain unchanged and free of sorryAx. The original Round26 scalar
interface files also match the saved checkpoint byte for byte. Seventeen audited
declarations (including derived interfaces and the assembled certificate) now
depend on sorryAx; they arise from exactly seven admitted source blocks.

DATA AND PROOF LINKAGE
The unchanged transcendental text supplies exact scalar arguments and endpoints.
The new grid_arithmetic.txt is 41,400,000 bytes: 50,000 blocks of 46 signed integer
records. Each record is exactly 18 ASCII bytes, namely a sign, 16 decimal digits,
and LF. For each cell, the first record is G*10^8 and the next 45 are K_j*10^8.
U and V are derived from the corresponding log arguments by subtracting
17/5,000,000,000. No separate distance table can drift out of agreement.

Lean elaborators embed these exact text bytes as ordinary immutable definitions,
never as generated proofs. The data definitions have no additional axioms.
The independent checker reads the shipped text, parses centers, weights and
knot heights from the pinned Lean certificate source, and verifies all five
rational families with exact FLINT rationals and Python integers. It uses no
floating-point tolerances and does not trust the generator's result.

Transcendental text SHA256:
89ce7741b3c7e5ac48d5f0d12c0ac2a07bf6a12ff47e836c5523e91be1429840
Grid arithmetic text SHA256:
5686a27a4e1290d335f04b902b4ce4a7906237cba6473de12341811c399ec5ea

REPRODUCING THE CHECKS
Extract the cumulative archive and enter its project directory.
Install Python 3.10+ and python-flint 0.9.0, then run:
  python3 numerical/fullgrid27/verify_grid.py
  python3 numerical/external26/verify_values.py \
    numerical/external26/transcendental_values.txt \
    --sha256 89ce7741b3c7e5ac48d5f0d12c0ac2a07bf6a12ff47e836c5523e91be1429840 \
    --report numerical/fullgrid27/transcendental_verification.json
  python3 numerical/fullgrid27/test_checker.py
The exact checker requires the extracted project sources and manifest; the
isolated Python download is not intended to run without those companion inputs.
No NumPy dependency is needed for verification (only for historical generation).

For Lean: use the included lean-toolchain (Lean 4.33.1) and pinned mathlib commit
0df444a360eaa60ab8c11dca51a86af692955474, install the mathlib cache, then:
  cd lean
  lake build FourValueFullGrid
  bash verify_fullgrid.sh
The script repeats the build, full axiom audit, both numerical checks and fault
injection tests. It writes fullgrid_verification.json with an explicitly
conditional PASS status. The old strict verify.sh and historical Round26 audit
remain preserved; their source-admission policies intentionally reject this
new externally checked branch. Use verify_fullgrid.sh for the current stage.

The complete cumulative archive includes all text data, checker programs,
source manifests, Lean sources, successful build/audit logs, and prior stages.
The new proof entry point is import FourValueFullGrid. The original FourValue
entry point is preserved unchanged for the previously proved core.

NEXT WORK
Global arithmetic allocation and the prime-sum/arithmetic lower bound, followed
by the final contradiction and full conditional audit. These remain genuine
proof work; completing this numerical stage does not establish them.
The earlier 3–10 hour estimate for this stage was too pessimistic: using a
generic expression soundness proof avoided millions of Lean table reductions.
That speedup does not by itself establish a comparable speedup for the remaining
symbolic arithmetic arguments.

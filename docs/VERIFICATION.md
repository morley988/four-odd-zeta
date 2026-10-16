# Verification boundary

## Statements

The final supplied-certificate statement is
`OddZeta.FourValue.irrational_zeta7_or_zeta9_or_zeta11_or_zeta13`
in [`FourValueFinal.lean`](../proof/lean/FourValueFinal.lean).
It concerns the ordinary classical zeta values, represented by real parts of Mathlib's `riemannZeta` and identified with the real zeta series.

In [`FourValueFinalContradiction.lean`](../proof/lean/FourValueFinalContradiction.lean),
`not_all_rational_of_certificates` and `irrational_one_of_four_of_certificates`
take the finite arithmetic and analytic certificates as explicit hypotheses.
The recorded audit finds only `propext`, `Classical.choice`, and `Quot.sound`
in their axiom dependencies. Neither depends on `sorryAx`.

## Eight numerical admissions

| Interface under `proof/lean/` | Count | External validation |
|---|---:|---|
| `FourValueExternalTranscendental.lean` | 2 | Logarithm/arctangent enclosures using Arb at 256 bits |
| `FourValueExternalArithmetic.lean` | 5 | Exact rational identities and analytic-grid inequalities |
| `FourValueExternalGlobalArithmetic.lean` | 1 | Exact finite arithmetic-grid predicate |

The final supplied-certificate wrapper **does depend on `sorryAx`**. The external programs validate the admitted statements independently; they do not manufacture Lean proof terms. The marked source locations and statement/file hashes are audited. Replacing the eight admissions by kernel-checkable proofs is further work.

## Recorded coverage

- 6,900,022 transcendental interval bounds.
- 50,000 analytic cells and 2,100,000 knot checks.
- 171,504 arithmetic cells and 3,810,331 reconstructed boxes.
- 1,873 named declarations in the final axiom audit.

The pinned prime-number-theorem dependency has two unrelated admissions in its Wiener module; the audited conditional arithmetic theorem does not depend on them. Thus a repository-wide textual search alone does not characterize a theorem's dependency closure.

## Evidence versus new execution

Files under `proof/numerical/final29/` and the Lean audit logs record the completed historical run. That run reused valid compiled artifacts; it was not an empty-cache rebuild of every source. Preserving these reports or successfully checking their hashes does not rerun their computations.

`scripts/check_package.py` checks delivered bytes. The three numerical verifiers check finite claims. `reproduce.sh` reruns numerical checks, builds the final dependency chain, and runs the axiom audit. These are different checks and must be reported separately.

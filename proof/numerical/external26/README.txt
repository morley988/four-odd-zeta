EXTERNAL TRANSCENDENTAL NUMERICAL CERTIFICATE — ROUND 26

INDEPENDENT CHECK (no Lean needed)
  python -m pip install python-flint==0.9.0
  python verify_values.py transcendental_values.txt --report verification.json
For a stricter precision rerun, add --precision 512.

The program streams the input and uses Arb outward-rounded interval arithmetic.
It accepts a claimed range only when the whole computed enclosure lies strictly
inside it. An inconclusive comparison fails. It checks every record, syntax,
positive rational arguments, exact counts, and end-of-file. No sampling is used.
For identity checking, also pass:
  --sha256 89ce7741b3c7e5ac48d5f0d12c0ac2a07bf6a12ff47e836c5523e91be1429840

TEXT FILE
transcendental_values.txt is an isolated ASCII file, 400,205,372 bytes. Its first
4,096 bytes are a JSON header padded with whitespace. Each following record is
58 bytes including its newline, with fields:
  kind numerator denominator signed_lower_numerator
A row 'L p q m' claims m/10^18 <= log(p/q) <= (m+5)/10^18.
A row 'A p q m' claims m/10^18 <= arctan(p/q) <= (m+5)/10^18, in radians.
Leading zeroes and signs make fields fixed-width; they do not change the numbers.
The upper endpoint is encoded exactly by the stated +5 rule, not omitted or
estimated. Every interval has width 5/10^18.

There are 5,700,022 logarithm rows followed by 1,200,000 arctangent rows:
- 22 shared constant logarithms;
- 50,000 cells, each with 24 J-expression logarithms and 90 distance logarithms;
- 50,000 cells, each with 24 arctangents.
The export covers the entire fixed grid, not just the Round25 three-cell batch.
It retains some repeated arguments for simple fixed indexing. Existing verified
pi, tail, and quadrature ingredients are not replaced with additional assumptions.

The generator uses the existing rational witness and 192-bit Arb arithmetic to
PROPOSE endpoints. The independent checker reads the resulting text afresh at
256-bit precision and does not import the generator or use its numerical output
as evidence. Both programs use Arb, so this is an independent checking program,
not an independent implementation of transcendental arithmetic.

LEAN TRUST BOUNDARY
lean/FourValueExternalTranscendental.lean contains exactly two explicitly marked
admitted proofs: log_values and atan_values. These are FINITE indexed families,
covering 5,700,022 and 1,200,000 table rows respectively. They are not assertions
about arbitrary arguments or arbitrary intervals. All occurrences of the marked
admission statement in the Lean source tree must be confined to this file.

The data loader reads the SAME text file, embeds ordinary immutable data into
Lean, and supplies no proof terms. Numerical arguments and endpoints in the
claims are obtained by the stated fixed-width decoding. Tables are chunked for
memory use. The ordinary definitions introduce no new axioms or admissions; rational
arithmetic retains the usual Lean foundational axioms.

FourValueExternalInterface.lean imports the previously proved core and the
isolated external file. Its adapters require proved equalities identifying a
chosen table row with the rational argument/endpoints used by an analytic proof.
There is no blanket assumption of the full grid certificate, no admission of
nonvanishing, and no admission of the final irrationality theorem.

AUDIT
  python numerical/external26/audit_assumptions.py lean
(run that command from the cumulative archive root).
The audit requires exactly two source tokens, the exact marker on the same lines,
the expected log/arctan theorem blocks, and the expected finite-family counts.
It also rejects unmarked admissions, custom axiom declarations, and native_decide
in all project Lean source files. The marker's suffix is
EXTERNAL_TRANSCENDENTAL_VALUE_CERTIFICATION_V1; inspect its two occurrences in
the isolated file. Count marked proof blocks separately from scalar records.

With pinned Lean/mathlib restored and python-flint installed:
  cd lean
  bash verify_external.sh
This builds and audits the explicitly CONDITIONAL interface, reruns the numerical
checker, checks the text hash, and verifies preservation of the original core.
The old verify.sh intentionally retains its strict no-admissions policy and will
reject this expanded source tree. It is NOT the verification command for the
external-numerics variant. Its Round25 evidence remains preserved.

The external variant is not fully Lean-certified: its new numerical interface
has sorryAx in its axiom dependency report. This is the requested explicit trust
boundary. The original 1,669 audited theorem declarations must remain free of
that dependency. The final four-value theorem and full grid assembly remain
unfinished; checking these values alone does not finish those steps.

REGENERATION
From the archive root:
  python numerical/external26/generate_values.py \
    --witness numerical/replay/round7_basis_witness.json \
    --out numerical/external26/transcendental_values.txt
Then rerun the checker and conditional audit. The published file hash identifies
this exact export. test_checker.py provides false-bound and truncated-file
negative controls. Generation and verification logs are included.

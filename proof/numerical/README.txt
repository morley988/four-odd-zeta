ROUND 22 NUMERICAL CERTIFICATE CHECKS

Run `bash reproduce.sh` from this directory after installing requirements.txt.
Run `bash verify.sh` in ../lean separately for the Lean build and axiom audit.
The numerical checker is not imported as a Lean axiom or oracle.

replay/ contains the recovered, unchanged Arb program and exact witness, plus
its regenerated grid and certificate. original/ contains the predecessor grid
and certificate used for exact replay comparison. The comparison verifies all
array entries, the original grid SHA256, and all certificate fields other than
elapsed runtime. audit_source_identity.py compares the centers, weights,
knots, denominator endpoints and normalization endpoints to the Lean sources.

exact_check.py checks every numerical enclosure with arbitrary-precision
integer arithmetic and explicit series error allowances. NumPy loads arrays
only; it does not perform certificate arithmetic in this checker. All maxima
and the quadrature are independently recomputed using Python integers and
fractions. exact_check_method.txt explains the enclosures and analytic cell
coverage. The saved logs and JSON results record the completed runs.

TRUST BOUNDARY
Successful Python/Arb checks do not discharge a Lean proposition. In the
Round 22 Lean bridge, FiniteKnotCertificate is still an explicit assumption.
The envelope, quadrature, interpolation, cell geometry and coarse infinite
tail have separate Lean proofs; finite transcendental enclosures still need
formalization. The full irrationality theorem and global arithmetic lower
bound are also not verified by this checkpoint.

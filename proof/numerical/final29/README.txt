Final contradiction and integration.

Main source: lean/FourValueFinal.lean
Explicit-hypothesis comparison: lean/FourValueFinalContradiction.lean
All eight earlier finite numerical admissions are retained unchanged; no new
admission is allowed by audit_final.py.

Reproduce all numerical checks and the final Lean build/axiom audit:
  python3 -m pip install python-flint==0.9.0
  bash numerical/final29/reproduce.sh

The pinned Lean and dependency versions are in lean/lean-toolchain,
lean/lakefile.toml and lean/lake-manifest.json.
A normal installation needs no container compatibility shim.

The published theorem is conditional on externally verified finite numerical
calculations. It is not an admission-free Lean formalization.

The reproduction script removes old success records before it begins and
regenerates numerical_rechecks.json from the three current verifier outputs.
A failed command stops the run; audit_final.py finish is an evidence/source
audit only and does not itself rerun Lean or the numerical verifiers.

Before rerunning (which regenerates reports), check the delivered file bytes
from the project root with: sha256sum --check SHA256_MANIFEST.txt

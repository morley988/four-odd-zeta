# Instructions for work on this repository

Read README.md and docs/VERIFICATION.md before changing proof-related files.

- The completed package lives in proof/; run Lean commands from proof/lean/.
- Preserve the eight explicitly authorized finite numerical admissions. Do not add admissions, weaken statements, or claim admission-free verification.
- Do not silently upgrade Lean, Mathlib, PrimeNumberTheoremAnd, or python-flint.
- Restore the certificate tables with scripts/restore_certificates.py before checks.
- Run scripts/check_package.py before reproduction; later generated reports may intentionally differ from the historical manifest.
- Distinguish hash checks, numerical verification, Lean compilation, and axiom audits in reports.
- Never infer successful fresh verification from the presence of historical logs.
- Preserve manuscript links and accurate correspondence to the final formal statements.
- Do not assign authorship, choose a license, change visibility, or create a public release without the owner's instruction.
- Exclude dependency/build caches and restored large tables from commits.

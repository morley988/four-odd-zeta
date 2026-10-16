# Reproducing the results

## 1. Restore and check delivered bytes

From the repository root, using Python 3.10 or newer:

```sh
python3 scripts/restore_certificates.py
python3 scripts/check_package.py
```

The restoration program verifies each compressed part, decompresses to a temporary file, checks the exact uncompressed size and SHA-256, and only then installs the table. It does not overwrite a differing existing output. Both restored tables are ignored by Git because their compressed representations are tracked instead.

The package checker verifies all 528 entries in the original Round 29 manifest. The compressed data contain the exact original bytes, with no numerical rounding or regeneration. The historical manifests cover `proof/`; they do not cover newly written repository documentation.

## 2. Install prerequisites

Use Linux, or WSL on Windows, with Git, Bash, Python 3.10+, and Lean's Elan toolchain manager. Install the exact toolchain specified by `proof/lean/lean-toolchain` (Lean 4.33.1). Do not upgrade the Lake manifest.

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r requirements.txt
cd proof/lean
elan toolchain install "$(cat lean-toolchain)"
lake env lean --version
cd ../..
```

The pinned dependencies are Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and PrimeNumberTheoremAnd `650d31264be65f4cd6e70c45d8b25d86d482a761`.
Network access is required for Lean, the Git dependencies and Mathlib's cache. Reserve several GB of disk space for dependencies and build artifacts. Exact clean-build time and memory requirements have not yet been benchmarked on GitHub-hosted runners.

## 3. Run the mathematical checks

```sh
cd proof
bash numerical/final29/reproduce.sh
```

The script stops on failure, removes stale success records first, reruns all three numerical checkers, refreshes the numerical summary, obtains dependency cache files, builds the final theorem dependency chain, and runs the final axiom audit.

Successful completion regenerates `numerical/final29/verification.json`, `build.exit`, `audit.exit`, and `lean/final_axiom_audit.log`. Inspect the new reports and the command exit status. A log from an interrupted run is not a successful run.

Normal Python execution is required: do not use `python -O`, because the existing checkers use assertions.

Historical numerical timings were approximately 20 seconds for transcendental bounds, 70 seconds for the analytic grid, and 242 seconds for the arithmetic grid on the original execution host. These are not GitHub-runner or clean-Lean-build benchmarks.

## Separate numerical checks

From `proof/`:

```sh
python3 numerical/external26/verify_values.py numerical/external26/transcendental_values.txt --report numerical/external26/verification_round29.json
python3 numerical/fullgrid27/verify_grid.py --out numerical/fullgrid27/verification_round29.json
python3 numerical/global28/verify_arithmetic.py
```

For an audit of *recorded* evidence and current source files, without rerunning Lean or numerical calculations:

```sh
python3 numerical/final29/audit_final.py finish
```

Run integrity checks before reproduction: checkers intentionally regenerate some reports, so their new bytes can differ from the delivered historical manifest. Use a separate checkout when preserving the historical evidence matters.

## Manuscript

From `manuscript/`, with a standard TeX Live installation, run `pdflatex -interaction=nonstopmode -halt-on-error Four_Odd_Zeta_Manuscript.tex` until cross-references stabilize (usually two or three passes).

## GitHub automation

The package-integrity workflow runs on push and pull request. It restores tables and checks hashes, without claiming a mathematical proof check. The numerical workflow is manually dispatched and runs the three finite verifiers. The full-reproduction workflow is also manual because compiling the complete Lean chain may require substantial runner time. No successful run of those workflows is claimed in advance.

## Codex Cloud setup

Select this repository when creating a Cloud environment. Ask Codex to read `AGENTS.md` and this document, install Python/Elan and the pinned dependencies, restore the tables, and run the integrity check. Full Lean reproduction is a separate explicit task. The working Lean directory is `proof/lean/`, not the repository root.

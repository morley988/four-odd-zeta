#!/usr/bin/env bash
# Conditional audit. Seven finite calculation families are externally checked.
set -eu
cd -- "$(dirname -- "$0")"
python3 ../numerical/fullgrid27/audit_checkpoint.py prepare
set +e
lake build FourValueFullGrid > fullgrid_build.log 2>&1
status=$?
set -e
printf '%s\n' "$status" > fullgrid_build.exit
if [ "$status" -ne 0 ]; then cat fullgrid_build.log; exit "$status"; fi
set +e
lake env lean FullGridAxiomAudit.lean > fullgrid_axiom_audit.log 2>&1
status=$?
set -e
printf '%s\n' "$status" > fullgrid_axiom_audit.exit
if [ "$status" -ne 0 ]; then cat fullgrid_axiom_audit.log; exit "$status"; fi
lake env lean FullGridKeyStatements.lean > fullgrid_key_statements.txt
python3 ../numerical/fullgrid27/verify_grid.py > ../numerical/fullgrid27/checker.log
python3 ../numerical/external26/verify_values.py ../numerical/external26/transcendental_values.txt --sha256 89ce7741b3c7e5ac48d5f0d12c0ac2a07bf6a12ff47e836c5523e91be1429840 --report ../numerical/fullgrid27/transcendental_verification.json > ../numerical/fullgrid27/transcendental_checker.log
python3 ../numerical/fullgrid27/test_checker.py
python3 ../numerical/fullgrid27/audit_checkpoint.py finish

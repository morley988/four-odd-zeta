#!/usr/bin/env bash
set -eu
cd -- "$(dirname -- "$0")"
python3 ../numerical/external26/prepare_external_audit.py
set +e
lake build FourValueExternalInterface > external_build.log 2>&1
status=$?
set -e
printf '%s\n' "$status" > external_build.exit
if [ "$status" -ne 0 ]; then cat external_build.log; exit "$status"; fi
set +e
lake env lean ExternalAxiomAudit.lean > external_axiom_audit.log 2>&1
status=$?
set -e
printf '%s\n' "$status" > external_axiom_audit.exit
if [ "$status" -ne 0 ]; then cat external_axiom_audit.log; exit "$status"; fi
lake env lean ExternalKeyStatements.lean > external_key_statements.txt
python3 ../numerical/external26/verify_values.py ../numerical/external26/transcendental_values.txt --sha256 89ce7741b3c7e5ac48d5f0d12c0ac2a07bf6a12ff47e836c5523e91be1429840 --report ../numerical/external26/verification.json > ../numerical/external26/checker_rebuild.log
python3 ../numerical/external26/audit_assumptions.py . --report ../numerical/external26/assumption_audit.json
python3 ../numerical/external26/verify_conditional_checkpoint.py

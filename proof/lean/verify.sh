#!/usr/bin/env bash
# Run from a normal Lean/Lake installation with the pinned dependencies restored.
set -eu
cd -- "$(dirname -- "$0")"
python3 prepare_audit.py
set +e
lake build > build.log 2>&1
build_status=$?
set -e
printf '%s\n' "$build_status" > build.exit
if [ "$build_status" -ne 0 ]; then
  cat build.log
  exit "$build_status"
fi
set +e
lake env lean AxiomAudit.lean > axiom_audit.log 2>&1
audit_status=$?
set -e
printf '%s\n' "$audit_status" > axiom_audit.exit
if [ "$audit_status" -ne 0 ]; then
  cat axiom_audit.log
  exit "$audit_status"
fi
lake env lean KeyStatements.lean > key_statements.txt
python3 verify_checkpoint.py

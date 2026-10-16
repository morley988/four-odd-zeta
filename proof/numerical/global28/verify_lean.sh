#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd -- "$(dirname -- "$0")/../.." && pwd)"
cd "$project_root"
rm -f numerical/global28/build.exit numerical/global28/axiom_audit.exit
python numerical/global28/audit_checkpoint.py prepare
cd lean
lake exe cache get
lake env python ../tools/serial_build.py FourValueFullGrid FourValueGlobalArithmeticComplete > global_arithmetic_build.log 2>&1
printf '0\n' > ../numerical/global28/build.exit
lake env lean GlobalArithmeticAxiomAudit.lean > global_arithmetic_axiom_audit.log 2>&1
printf '0\n' > ../numerical/global28/axiom_audit.exit
cd ..
python numerical/global28/audit_checkpoint.py finish

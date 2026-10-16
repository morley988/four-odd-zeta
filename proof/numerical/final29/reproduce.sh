#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd -- "$(dirname -- "$0")/../.." && pwd)"
cd "$project_root"
rm -f numerical/final29/build.exit numerical/final29/audit.exit numerical/final29/numerical_rechecks.json numerical/final29/verification.json
python3 numerical/external26/verify_values.py numerical/external26/transcendental_values.txt --report numerical/external26/verification_round29.json
python3 numerical/fullgrid27/verify_grid.py --out numerical/fullgrid27/verification_round29.json
python3 numerical/global28/verify_arithmetic.py
python3 numerical/final29/collect_rechecks.py
python3 numerical/final29/audit_final.py prepare
cd lean
lake exe cache get
lake env python3 ../tools/serial_build.py FourValueFinal FourValueGlobalArithmeticComplete > final_build.log 2>&1
printf '0\n' > ../numerical/final29/build.exit
lake env lean FinalAxiomAudit.lean > final_axiom_audit.log 2>&1
printf '0\n' > ../numerical/final29/audit.exit
cd ..
python3 numerical/final29/audit_final.py finish

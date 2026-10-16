#!/usr/bin/env bash
set -eu
for mod in FourValueBatchTools FourValueBatchEnclosures FourValueBatchFirstCell FourValueBatchEnclosures5669 FourValueBatchCell5669 FourValueBatchEnclosures49999 FourValueBatchCell49999 FourValueBatch; do
  ./run_lean.sh build "$mod" > "batch25/lake_${mod}.log" 2>&1
done
./run_lean.sh env bash verify.sh > work/Four_Value_Lean_Round20/verification_run.log 2>&1

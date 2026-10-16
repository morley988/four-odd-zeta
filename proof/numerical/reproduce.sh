#!/usr/bin/env bash
set -eu
cd -- "$(dirname -- "$0")"
python3 replay/round7_real_certificate.py
python3 compare_replay.py
python3 audit_source_identity.py ../lean
python3 exact_check.py

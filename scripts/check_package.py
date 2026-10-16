#!/usr/bin/env python3
"""Check original package bytes; does not rerun mathematical verification."""
from pathlib import Path
import hashlib, json, sys
ROOT = Path(__file__).resolve().parents[1] / 'proof'
manifest = json.loads((ROOT / 'SHA256_MANIFEST.json').read_text())
errors = []
for relative, expected in manifest.items():
    path = ROOT / relative
    if not path.is_file():
        errors.append(f'MISSING {relative}'); continue
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''): h.update(chunk)
    if h.hexdigest() != expected: errors.append(f'MISMATCH {relative}')
if errors:
    print('\n'.join(errors), file=sys.stderr)
    raise SystemExit(1)
print(f'PASS: {len(manifest)} original package entries match SHA-256.')
print('Integrity only: numerical checks and Lean were not rerun by this command.')

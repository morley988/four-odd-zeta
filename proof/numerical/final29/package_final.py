#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,zipfile
P=Path(__file__).resolve().parents[2];D=P.parent/'deliverables29';D.mkdir(exist_ok=True)
v=json.loads((P/'numerical/final29/verification.json').read_text())
assert v['final_contradiction_compiled'] and v['new_admissions']==0
skip={'SHA256_MANIFEST.txt','SHA256_MANIFEST.json'}
files=[p for p in sorted(P.rglob('*')) if p.is_file() and not any(x in {'.lake','.git','__pycache__'} for x in p.relative_to(P).parts) and p.name not in skip]
manifest={str(p.relative_to(P)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
(P/'SHA256_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
(P/'SHA256_MANIFEST.txt').write_text(''.join(h+'  '+n+'\n' for n,h in manifest.items()))
archive=D/'Four_Value_Lean_Round29.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in files+[P/'SHA256_MANIFEST.json',P/'SHA256_MANIFEST.txt']:z.write(p,str(Path(P.name)/p.relative_to(P)))
for name in ['Four_Value_Final_Report_2026-10-15.txt']:
 (D/name).write_bytes((P/name).read_bytes())
print(archive,archive.stat().st_size)

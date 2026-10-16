from pathlib import Path
import json,hashlib,shutil
p=Path('work/Four_Value_Lean_Round20/lean')
v=json.loads((p/'verification.json').read_text())
assert v['theorem_count']==1415
(p/'round24_verification.json').write_text(json.dumps(v,indent=2)+'\n')
(p/'baseline_audit_declarations.json').write_bytes((p/'audit_declarations.json').read_bytes())
base={n:h for n,h in v['source_sha256'].items() if n not in ['FourValue.lean','AxiomAudit.lean','KeyStatements.lean']}
assert len(base)==221
for n,h in base.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
(p/'baseline_preservation.json').write_text(json.dumps(base,indent=2)+'\n')
s=(p/'prepare_audit.py').read_text().replace('FourValueFast*.lean','FourValueBatch*.lean')
s=s.replace("prefix='OddZeta.FourValue.Fast.'+('Interval.' if p.name=='FourValueFastInterval.lean' else '')", "prefix=re.search(r'^namespace (.+)$',p.read_text(),re.M)[1]+'.'")
(p/'prepare_audit.py').write_text(s)
mods=sorted(f.stem for f in p.glob('FourValueBatch*.lean'))
s=(p/'lakefile.toml').read_text().replace('roots = [','roots = ['+', '.join('"'+m+'"' for m in mods)+', ')
(p/'lakefile.toml').write_text(s)
s=(p/'FourValue.lean').read_text();(p/'FourValue.lean').write_text('\n'.join('import '+m for m in mods)+'\n'+s)
with (p/'KeyStatements.lean').open('a') as f:
 for k in [0,5669,49999]:f.write(f'\n#check OddZeta.FourValue.Batch.Cell{k}.all_knots_on_'+('first_cell' if k==0 else 'cell')+'\n')
s=(p/'verify_checkpoint.py').read_text();a=s.index('    "scope":');b=s.index('\n',a)
s=s[:a]+'    "scope": "Round 25: end-to-end certificate batch for actual grid cells 0, 5669, and 49999, including all 42 knot inequalities and whole-cell real bounds. Full grid certificate and final theorem remain incomplete.",'+s[b:]
s=s.replace('    "concrete_grid_certificate_instantiated": False,','    "end_to_end_certificate_batch_verified": build_ok and audit_ok and not forbidden,\n    "certified_grid_cells": [0, 5669, 49999],\n    "total_grid_cells": 50000,\n    "concrete_grid_certificate_instantiated": False,')
(p/'verify_checkpoint.py').write_text(s)
if (p/'BatchGTest.lean').exists():shutil.move(p/'BatchGTest.lean','batch25/BatchGTest.lean')
print('Round25 audit configured:',len(mods),'new modules')

from pathlib import Path
import re,json
old=json.loads(Path('baseline_audit_declarations.json').read_text())
names=list(old); by_file={}
for p in sorted(Path('.').glob('FourValueBatch*.lean')):
 ds=re.findall(r'(?m)^theorem\s+([^\s({:]+)',p.read_text())
 prefix=re.search(r'^namespace (.+)$',p.read_text(),re.M)[1]+'.'
 ns=[prefix+d for d in ds]
 by_file[p.name]=ns; names+=ns
assert len(names)==len(set(names))
Path('audit_declarations.json').write_text(json.dumps(names,indent=2)+'\n')
Path('audit_modules.json').write_text(json.dumps(by_file,indent=2)+'\n')
Path('AxiomAudit.lean').write_text('import FourValue\n\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
print(json.dumps({'theorems':len(names),'new_theorems':len(names)-len(old),'new_modules':len(by_file)}))

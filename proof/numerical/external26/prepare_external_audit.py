from pathlib import Path
import re,json,hashlib
p=Path(__file__).resolve().parents[2]/'lean'
base=json.loads((p/'round25_verification.json').read_text())
for n,h in base['source_sha256'].items():
 assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
names=json.loads((p/'round25_audit_declarations.json').read_text());assert len(names)==1669
new=[]
for name in ['FourValueExternalTranscendental.lean','FourValueExternalInterface.lean']:
 s=(p/name).read_text();prefix=re.search(r'^namespace (.+)$',s,re.M)[1]+'.'
 new += [prefix+x for x in re.findall(r'^theorem\s+([^\s({:]+)',s,re.M)]
assert len(new)==4
data=['OddZeta.FourValue.External.'+x for x in ['values','argument','lower','upper']]
allnames=names+new+data
(p/'external_audit_groups.json').write_text(json.dumps({'conditional_theorems':new,'data_definitions':data},indent=2)+'\n')
(p/'external_audit_declarations.json').write_text(json.dumps(allnames,indent=2)+'\n')
(p/'ExternalAxiomAudit.lean').write_text('import FourValueExternalInterface\n\n'+'\n'.join('#print axioms '+n for n in allnames)+'\n')
(p/'ExternalKeyStatements.lean').write_text('import FourValueExternalInterface\n\n'+'\n'.join('#check '+n for n in new)+'\n')
print(json.dumps({'core_declarations':len(names),'new_declarations':len(new),'total':len(allnames)}))

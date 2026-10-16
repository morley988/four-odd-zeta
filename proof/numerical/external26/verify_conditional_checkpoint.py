"""Audit the explicitly conditional Round26 checkpoint; never marks it fully proved."""
from pathlib import Path
import json,re,hashlib
from audit_assumptions import audit
root=Path(__file__).resolve().parents[2];p=root/'lean';here=Path(__file__).resolve().parent
base=json.loads((p/'round25_verification.json').read_text());core=json.loads((p/'round25_audit_declarations.json').read_text())
for n,h in base['source_sha256'].items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
source=audit(p);names=json.loads((p/'external_audit_declarations.json').read_text())
entries=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))",(p/'external_axiom_audit.log').read_text())
ax={n:[s.strip() for s in ds.split(',') if s.strip()] for n,ds,_ in entries}
assert len(ax)==len(entries)==len(names)==1677
assert set(ax)==set(names)
allowed={'propext','Classical.choice','Quot.sound'}
for n in core:assert set(ax[n])<=allowed,n
groups=json.loads((p/'external_audit_groups.json').read_text())
new=set(groups['conditional_theorems'])
for n in groups['data_definitions']:assert set(ax[n])<=allowed,n
assert not ax['OddZeta.FourValue.External.values']
for n in new:assert set(ax[n])<=allowed|{'sorryAx'} and 'sorryAx' in ax[n],n
num=json.loads((here/'verification.json').read_text())
assert num['status']=='PASS' and num['complete'] and num['total_bounds_checked']==6900022
sha=hashlib.file_digest((here/'transcendental_values.txt').open('rb'),'sha256').hexdigest()
assert sha==num['sha256']=='89ce7741b3c7e5ac48d5f0d12c0ac2a07bf6a12ff47e836c5523e91be1429840'
assert int((p/'external_build.exit').read_text())==0
assert int((p/'external_axiom_audit.exit').read_text())==0
r={'status':'PASS_WITH_EXPLICIT_EXTERNAL_NUMERICAL_ASSUMPTIONS','fully_lean_certified':False,'full_four_value_zeta_theorem_verified':False,'full_grid_certificate_assembled':False,'all_grid_transcendental_rows_externally_verified':True,'explicit_assumption_count':2,'log_bounds':5700022,'atan_bounds':1200000,'core_declarations_unchanged_and_without_sorryAx':len(core),'all_round25_lean_sources_byte_identical':True,'total_audited_declarations':len(names),'new_declarations_depending_on_sorryAx':sorted(new),'source_audit':source,'table_sha256':sha,'numerical_verification':num,'axioms':ax}
(p/'external_verification.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:v for k,v in r.items() if k!='axioms'},indent=2))

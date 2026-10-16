#!/usr/bin/env python3
"""Audit unchanged baseline, marked finite admissions, and fresh final axiom log."""
from pathlib import Path
import json,re,hashlib,sys,argparse
P=Path(__file__).resolve().parents[2];L=P/'lean';D=Path(__file__).resolve().parent
sys.path.insert(0,str(P/'numerical/global28'))
from audit_checkpoint import source
BASE=json.loads((D/'baseline28.json').read_text())
STANDARD={'propext','Classical.choice','Quot.sound'}
NEW=['final_rate_gap','not_all_rational_of_certificates','realZeta','realZeta_cast','realZeta_eq_re','irrational_one_of_four_of_certificates','not_all_four_zeta_rational','irrational_one_of_four','irrational_zeta7_or_zeta9_or_zeta11_or_zeta13']
NEW=['OddZeta.FourValue.'+s for s in NEW]
CONDITIONAL=set(NEW[-3:])
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def sources():
 s=source()
 for name,h in BASE['lean_source_sha256'].items():assert sha(L/name)==h,name
 return s
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['prepare','finish']);args=ap.parse_args()
 so=sources();names=list(BASE['axioms'])+NEW
 if args.mode=='prepare':
  (L/'FinalAxiomAudit.lean').write_text('import FourValueFinal\nimport FourValueGlobalArithmeticComplete\nimport FourValueFullGrid\n\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
  print('Prepared',len(names),'declaration audits')
 else:
  log=(L/'final_axiom_audit.log').read_text();assert 'error:' not in log
  es=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))",log)
  ax={n:[s.strip() for s in a.split(',') if s.strip()] for n,a,_ in es}
  assert len(ax)==len(es)==len(names) and set(ax)==set(names)
  for n,a in BASE['axioms'].items():assert set(ax[n])==set(a),n
  for n in NEW:
   assert set(ax[n])<=STANDARD|({'sorryAx'} if n in CONDITIONAL else set()),(n,ax[n])
   assert ('sorryAx' in ax[n])==(n in CONDITIONAL),(n,ax[n])
  for f in ['build.exit','audit.exit']:assert (D/f).read_text().strip()=='0'
  numerics=json.loads((D/'numerical_rechecks.json').read_text())
  tr=numerics['transcendental'];gr=numerics['analytic_grid'];ar=numerics['arithmetic']
  assert tr['status']=='PASS' and tr['complete'] and tr['total_bounds_checked']==6900022
  assert tr['sha256']==sha(P/'numerical/external26/transcendental_values.txt')
  assert gr['status']=='PASS' and gr['complete'] and gr['cells']==50000
  assert gr['grid_sha256']==sha(P/'numerical/fullgrid27/grid_arithmetic.txt')
  assert gr['transcendental_sha256']==tr['sha256']
  assert ar['passed'] and ar['cells']==171504 and ar['boxes_including_zero_capacity']==3810331
  assert ar['data_sha256']==sha(P/'numerical/global28/arithmetic_cells.txt')
  result=dict(status='PASS_WITH_EIGHT_EXTERNAL_FINITE_CALCULATION_ADMISSIONS',final_contradiction_compiled=True,fully_lean_certified=False,new_admissions=0,total_project_admissions=8,total_audited_declarations=len(names),unchanged_round28_lean_sources=len(BASE['lean_source_sha256']),new_declarations=NEW,source_audit=so,numerical_rechecks=numerics,axioms=ax,lean_source_sha256={p.name:sha(p) for p in sorted(L.glob('*.lean'))})
  (D/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
  print(json.dumps({k:v for k,v in result.items() if k not in ['axioms','lean_source_sha256']},indent=2))

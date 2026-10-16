#!/usr/bin/env python3
"""Audit the released arithmetic checkpoint's source and Lean axiom output."""
from pathlib import Path
import sys,re,json,hashlib,argparse
P=Path(__file__).resolve().parents[2];L=P/'lean';H=Path(__file__).resolve().parent
sys.path.insert(0,str(P/'numerical/external26'))
from audit_assumptions import clean
STANDARD={'propext','Classical.choice','Quot.sound'}
PERMITTED={'FourValueExternalTranscendental.lean':('EXTERNAL_TRANSCENDENTAL_VALUE_CERTIFICATION_V1',2),'FourValueExternalArithmetic.lean':('EXTERNAL_FINITE_RATIONAL_CERTIFICATION_V1',5),'FourValueExternalGlobalArithmetic.lean':('EXTERNAL_GLOBAL_ARITHMETIC_CERTIFICATE_V1',1)}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def source():
 baseline=json.loads((H/'baseline_sources.json').read_text())
 for name,h in baseline.items():assert sha(L/name)==h,name
 hits=[]
 for p in sorted(L.glob('*.lean')):
  raw=p.read_text();s=clean(raw)
  tokens=list(re.finditer(r'\b(?:sorry|admit|axiom|native_decide)\b',s))
  marks=[(i,line.strip()) for i,line in enumerate(raw.splitlines(),1) if any(m in line for m,_ in PERMITTED.values())]
  if p.name in PERMITTED:
   marker,count=PERMITTED[p.name];assert len(tokens)==len(marks)==count,p.name
   for tok,(ln,line) in zip(tokens,marks):
    assert tok[0]=='sorry' and s[:tok.start()].count('\n')+1==ln
    assert line=='sorry -- '+marker
    hits.append(dict(file=p.name,line=ln,marker=marker))
  else:assert not tokens and not marks,p.name
 pinned=json.loads((H/'external_statement_hashes.json').read_text())
 for name,h in pinned.items():assert sha(L/name)==h,name
 assert len(hits)==8
 return dict(status='PASS',admissions=8,locations=hits,unchanged_prior_lean_files=len(baseline))
def prepare():
 source()
 old=json.loads((L/'fullgrid_verification.json').read_text())['axioms']
 baseline=json.loads((H/'baseline_sources.json').read_text());new=[]
 for p in sorted(L.glob('*.lean')):
  if p.name in baseline:continue
  s=clean(p.read_text());ns=re.search(r'^namespace\s+(\S+)',s,re.M)
  if not ns:continue
  prefix=ns[1]+'.'
  new += [prefix+n for n in re.findall(r'^(?:noncomputable\s+)?(?:theorem|def|structure)\s+([^\s({:]+)',s,re.M)]
 assert len(new)==len(set(new)),new
 names=list(old)+new;assert len(names)==len(set(names))
 (H/'audit_names.json').write_text(json.dumps(names,indent=2)+'\n')
 (H/'new_declarations.json').write_text(json.dumps(new,indent=2)+'\n')
 (L/'GlobalArithmeticAxiomAudit.lean').write_text('import FourValueFullGrid\nimport FourValueGlobalArithmeticComplete\n\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
 print(json.dumps(dict(prior=len(old),new=len(new),total=len(names))))
def finish():
 so=source();names=json.loads((H/'audit_names.json').read_text())
 log=(L/'global_arithmetic_axiom_audit.log').read_text();assert 'error:' not in log
 entries=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))",log)
 ax={n:[a.strip() for a in ds.split(',') if a.strip()] for n,ds,_ in entries}
 assert len(ax)==len(entries)==len(names) and set(ax)==set(names)
 prior=json.loads((L/'fullgrid_verification.json').read_text())['axioms']
 for n,a in prior.items():assert set(ax[n])==set(a),(n,ax[n],a)
 conditional={'OddZeta.FourValue.ArithmeticCertificate.'+n for n in ('external_grid_certificate','global_arithmetic_lower')}
 for n in set(names)-set(prior):
  assert set(ax[n])<=STANDARD|({'sorryAx'} if n in conditional else set()),(n,ax[n])
  assert ('sorryAx' in ax[n])==(n in conditional),(n,ax[n])
 v=json.loads((H/'verification.json').read_text());assert v['passed'] and v['cells']==171504 and v['data_sha256']==sha(H/'arithmetic_cells.txt')
 from fractions import Fraction as F
 assert F(v['main_integral_lower'])>=-114800 and F(v['normalized_with_small_prime_allowance'])>F(-288,25)
 neg=json.loads((H/'negative_controls.json').read_text());assert neg['status']=='PASS'
 assert (H/'build.exit').read_text().strip()=='0'
 assert (H/'axiom_audit.exit').read_text().strip()=='0'
 report=dict(status='PASS_WITH_EXPLICIT_EXTERNAL_NUMERICAL_ASSUMPTIONS',stage='Global arithmetic lower bound',stage_complete=True,fully_lean_certified=False,full_four_value_zeta_theorem_verified=False,global_lower_rate='-288/25',source_audit=so,lean_source_sha256={f.name:sha(f) for f in sorted(L.glob('*.lean'))},total_audited_declarations=len(names),new_public_declarations=len(names)-len(prior),new_conditional_declarations=sorted(conditional),numerical_verification=v,negative_controls=neg,axioms=ax)
 (L/'global_arithmetic_verification.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items() if k not in ('axioms','lean_source_sha256')},indent=2))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['prepare','finish']);args=ap.parse_args();prepare() if args.mode=='prepare' else finish()

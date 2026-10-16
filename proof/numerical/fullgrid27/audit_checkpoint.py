#!/usr/bin/env python3
"""Structural source and kernel-axiom audit of the conditional full-grid proof."""
from pathlib import Path
import argparse,hashlib,json,re,sys
P=Path(__file__).resolve().parents[2];L=P/'lean';H=Path(__file__).resolve().parent
sys.path.insert(0,str(P/'numerical/external26'))
from audit_assumptions import clean
FILES=['FourValueFullGridExpressions.lean','FourValueFullGridData.lean','FourValueExternalArithmetic.lean','FourValueFullGrid.lean']
STANDARD={'propext','Classical.choice','Quot.sound'}

def source_audit():
 old=json.loads((L/'round25_verification.json').read_text())['source_sha256']
 old.update(json.loads((H/'round26_sources.json').read_text()))
 for n,h in old.items():assert hashlib.sha256((L/n).read_bytes()).hexdigest()==h,n
 permitted={'FourValueExternalTranscendental.lean':('EXTERNAL_TRANSCENDENTAL_VALUE_CERTIFICATION_V1',2),'FourValueExternalArithmetic.lean':('EXTERNAL_FINITE_RATIONAL_CERTIFICATION_V1',5)}
 hits=[]
 for p in sorted(L.glob('*.lean')):
  s=p.read_text();c=clean(s)
  tokens=list(re.finditer(r'\b(?:sorry|admit|axiom|native_decide)\b',c))
  markers=[(i,x.strip()) for i,x in enumerate(s.splitlines(),1) if any(m in x for m,_ in permitted.values())]
  if p.name in permitted:
   marker,count=permitted[p.name]
   assert len(tokens)==len(markers)==count,p.name
   for tok,(ln,line) in zip(tokens,markers):
    assert tok[0]=='sorry' and c[:tok.start()].count('\n')+1==ln
    assert line=='sorry -- '+marker
    hits.append({'file':p.name,'line':ln,'marker':marker})
  else: assert not tokens and not markers,p.name
 # Pin exact admitted statements, including their full finite domains and rational predicates.
 manifest=json.loads((H/'source_manifest.json').read_text())
 for n in permitted:assert hashlib.sha256((L/n).read_bytes()).hexdigest()==manifest['lean/'+n]
 return {'status':'PASS','explicit_assumptions':len(hits),'locations':hits,'preserved_lean_sources':len(old),'old_core_theorems':1669}

def prepare():
 source_audit()
 names=json.loads((L/'external_audit_declarations.json').read_text());new=[];data=[]
 for file in FILES:
  s=(L/file).read_text();prefix='OddZeta.FourValue.FullGrid.'
  new.extend(prefix+x for x in re.findall(r'^theorem\s+([^\s({:]+)',s,re.M))
  data.extend(prefix+x for x in re.findall(r'^(?:noncomputable )?def\s+([^\s({:]+)',s,re.M))
 names+=new+data
 assert len(names)==len(set(names))
 (H/'audit_names.json').write_text(json.dumps(names,indent=2)+'\n')
 (H/'audit_groups.json').write_text(json.dumps({'new_theorems':new,'new_definitions':data},indent=2)+'\n')
 (L/'FullGridAxiomAudit.lean').write_text('import FourValueFullGrid\n\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
 (L/'FullGridKeyStatements.lean').write_text('import FourValueFullGrid\n\n'+'\n'.join('#check OddZeta.FourValue.FullGrid.'+n for n in ['certificate','finite_knots','all_knots','envelope_bound','numerical_rate'])+'\n')
 print(json.dumps({'audit_declarations':len(names),'new_theorems':len(new),'new_definitions':len(data)}))

def finish():
 source=source_audit();names=json.loads((H/'audit_names.json').read_text())
 entries=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))",(L/'fullgrid_axiom_audit.log').read_text())
 ax={n:[a.strip() for a in ds.split(',') if a.strip()] for n,ds,_ in entries}
 assert len(ax)==len(entries)==len(names) and set(ax)==set(names)
 oldconditional=set(json.loads((L/'external_audit_groups.json').read_text())['conditional_theorems'])
 expected=oldconditional|{'OddZeta.FourValue.FullGrid.'+n for n in ['Expr.contains','expression_rows','expression_upper','distances','pair_upper','knot_arithmetic','g_bound','log_bound','certificate','finite_knots','all_knots','envelope_bound','numerical_rate']}
 for n,a in ax.items():
  assert set(a)<=STANDARD|({'sorryAx'} if n in expected else set()),(n,a)
  assert ('sorryAx' in a)==(n in expected),(n,a)
 assert not ax['OddZeta.FourValue.FullGrid.gridValues']
 for file in ['fullgrid_build.exit','fullgrid_axiom_audit.exit']:assert (L/file).read_text().strip()=='0',file
 trans=json.loads((H/'transcendental_verification.json').read_text());grid=json.loads((H/'verification.json').read_text());negative=json.loads((H/'negative_controls.json').read_text())
 assert trans['complete'] and trans['status']=='PASS' and trans['total_bounds_checked']==6900022
 assert grid['complete'] and grid['status']=='PASS' and grid['cells']==50000 and grid['knot_checks']==2100000
 assert negative['status']=='PASS'
 r={'status':'PASS_WITH_EXPLICIT_EXTERNAL_NUMERICAL_ASSUMPTIONS','stage':'full-grid linkage and remaining calculation interfaces','stage_complete':True,'fully_lean_certified':False,'full_four_value_zeta_theorem_verified':False,'full_grid_certificate_assembled':True,'finite_and_infinite_contour_bounds_linked':True,'numerical_determinant_rate_linked':True,'explicit_assumption_count':7,'transcendental_assumption_families':2,'rational_assumption_families':5,'core_declarations_unchanged_and_without_sorryAx':1669,'total_audited_declarations':len(names),'conditional_declarations':sorted(expected),'source_audit':source,'transcendental_verification':trans,'rational_verification':grid,'negative_controls':negative,'axioms':ax}
 (L/'fullgrid_verification.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='axioms'},indent=2))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['prepare','finish']);a=ap.parse_args();prepare() if a.mode=='prepare' else finish()

"""Check source placement and shape of the two explicit numerical assumptions.
Usage: python audit_assumptions.py ../lean
This is a structural audit, not a proof of the numerical claims.
"""
import argparse,json,re,hashlib
from pathlib import Path

def clean(s):
 out=[];i=0;depth=0;string=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif string:
   if s[i]=='\\':i+=2
   elif s[i]=='"':string=False;i+=1
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):
   end=s.find('\n',i);i=len(s) if end<0 else end
  elif s[i]=='"':string=True;i+=1
  else:out.append(s[i]);i+=1
 if depth or string:raise ValueError('Unterminated comment/string')
 return ''.join(out)

def audit(root):
 permitted='FourValueExternalTranscendental.lean';marker='sorry'+' -- EXTERNAL_TRANSCENDENTAL_VALUE_CERTIFICATION_V1'
 files=sorted(root.glob('*.lean'));hits=[];marker_hits=[]
 for p in files:
  s=p.read_text();c=clean(s)
  for m in re.finditer(r'\b(?:sorry|admit|axiom|native_decide)\b',c):
   line=c[:m.start()].count('\n')+1
   if m[0]!='sorry' or p.name!=permitted:raise ValueError(f'Forbidden token {p.name}:{line}: {m[0]}')
   hits.append({'file':p.name,'line':line})
  for line,text in enumerate(s.splitlines(),1):
   if marker in text:
    if p.name!=permitted or text.strip()!=marker:raise ValueError('Marker outside exact allowed statement')
    marker_hits.append({'file':p.name,'line':line})
 if len(hits)!=2 or hits!=marker_hits:raise ValueError(f'Expected exactly two marked holes: {hits}, {marker_hits}')
 s=(root/permitted).read_text()
 expected=[('log_values','Real.log','Fin logCount'),('atan_values','Real.arctan','Fin atanCount')]
 for name,fn,index in expected:
  m=re.search(r'theorem '+name+r'\b(.*?)(?=\n/--|\nend )',s,re.S)
  if not m or fn not in m[1] or index not in m[1] or m[1].count(marker)!=1 or m[1].count(':= by')!=1:raise ValueError(f'Unexpected claim structure: {name}')
 if 'def logCount : Nat := 5700022' not in s or 'def atanCount : Nat := 1200000' not in s:raise ValueError('Wrong finite bounds')
 return {'status':'PASS','explicit_assumption_count':2,'locations':hits,'log_value_count':5700022,'atan_value_count':1200000,'total_value_count':6900022,'only_file':permitted,'lean_file_sha256':hashlib.sha256(s.encode()).hexdigest(),'scope':'Source audit; does not replace numerical checking or kernel axiom audit'}

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('lean_directory',type=Path);p.add_argument('--report',type=Path,default=Path('assumption_audit.json'));a=p.parse_args()
 r=audit(a.lean_directory);a.report.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))

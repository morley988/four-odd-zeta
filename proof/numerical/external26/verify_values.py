"""Independent streaming Arb verification of every exact range in the text file.
Install: python -m pip install python-flint==0.9.0
Run: python verify_values.py transcendental_values.txt --report verification.json
No generator, Lean installation, numpy, or network access is needed to check.
"""
import argparse,hashlib,json,sys,time
from pathlib import Path
import flint
from flint import arb,ctx

def verify(path,precision,expected_sha=None):
 if precision<128:raise ValueError('Use at least 128 bits')
 ctx.prec=precision;start=time.monotonic();digest=hashlib.sha256();counts={'L':0,'A':0}
 with path.open('rb') as f:
  head=f.read(4096);digest.update(head);meta=json.loads(head.decode('ascii').strip())
  if meta['format']!='FV_TRANS_V1' or meta['header_bytes']!=4096 or meta['record_bytes']!=58:raise ValueError('Wrong format')
  if meta['scale']!=10**18 or meta['upper_minus_lower_numerator']!=5:raise ValueError('Wrong endpoint encoding')
  if (meta['cells'],meta['full_grid_cells'],meta['log_count'],meta['atan_count'])!=(50000,50000,5700022,1200000):raise ValueError('Not the full 50,000-cell export')
  total=meta['log_count']+meta['atan_count'];index=0
  while block:=f.read(58*10000):
   digest.update(block)
   if len(block)%58:raise ValueError('Truncated record')
   for pos in range(0,len(block),58):
    row=block[pos:pos+58];kind=chr(row[0]);expected='L' if index<meta['log_count'] else 'A'
    if kind!=expected or row[1:2]!=b' ' or row[18:19]!=b' ' or row[35:36]!=b' ' or row[57:58]!=b'\n':raise ValueError(f'Malformed record {index}')
    if not row[2:18].isdigit() or not row[19:35].isdigit() or row[36:37] not in (b'+',b'-') or not row[37:57].isdigit():raise ValueError(f'Invalid digits {index}')
    n=int(row[2:18]);d=int(row[19:35]);lo=int(row[36:57])
    if n<=0 or d<=0:raise ValueError(f'Nonpositive argument {index}')
    q=arb(n)/d;v=q.log() if kind=='L' else q.atan()
    lower=arb(lo)/10**18;upper=arb(lo+5)/10**18
    # Arb comparisons succeed only when the interval difference is strictly positive.
    if not v.is_finite() or not (v-lower>0 and upper-v>0):
     raise ValueError(f'FAIL or inconclusive at row {index}: {kind}({n}/{d}) in [{lo}/10^18,{lo+5}/10^18]; Arb={v}')
    counts[kind]+=1;index+=1
   if index%250000==0:print(json.dumps({'checked':index,'total':total,'seconds':round(time.monotonic()-start,2)}),flush=True)
  if index!=total:raise ValueError(f'Wrong record count {index}, expected {total}')
 sha=digest.hexdigest()
 if expected_sha is not None and sha!=expected_sha:raise ValueError('SHA256 mismatch')
 return {'status':'PASS','complete':True,'log_bounds_checked':counts['L'],'atan_bounds_checked':counts['A'],'total_bounds_checked':index,'sha256':sha,'precision_bits':precision,'python_flint_version':flint.__version__,'python_version':sys.version,'seconds':time.monotonic()-start,'method':'Arb outward-rounded ball arithmetic; strict containment in exact rational claimed intervals','formal_lean_certification':False}

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('file',type=Path);p.add_argument('--precision',type=int,default=256);p.add_argument('--sha256');p.add_argument('--report',type=Path,default=Path('verification.json'));a=p.parse_args()
 try:r=verify(a.file,a.precision,a.sha256)
 except Exception as e:
  r={'status':'FAIL','complete':False,'error':str(e)};a.report.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),file=sys.stderr);sys.exit(1)
 a.report.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()

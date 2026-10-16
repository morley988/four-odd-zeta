#!/usr/bin/env python3
"""Exact, independently runnable verification of the five finite Lean families.
Requires python-flint. No floating point arithmetic. The separate verify_values.py
checks the transcendental intervals with Arb. Source hashes bind this checker to
one reviewed Lean interface; changed sources require a new review and manifest.
"""
import argparse, ast, hashlib, json, mmap, re, time
from pathlib import Path
from flint import fmpq as Q
N=50000; LC=5700022; AC=1200000; S=10**18
TRANS_SHA='89ce7741b3c7e5ac48d5f0d12c0ac2a07bf6a12ff47e836c5523e91be1429840'
GRID_SHA='5686a27a4e1290d335f04b902b4ce4a7906237cba6473de12341811c399ec5ea'

def require(ok, message):
 if not ok: raise ValueError(message)
def sha(p):
 with p.open('rb') as f: return hashlib.file_digest(f,'sha256').hexdigest()
def lists(source, name):
 body=source.split('def '+name+' :',1)[1].split(':=',1)[1].split('\n]',1)[0]+'\n]'
 body=re.sub(r'\((-?\d+)\s*/\s*(\d+)\s*:\s*ℚ\)',lambda m:repr(m[1]+'/'+m[2]),body)
 return ast.literal_eval(body.strip())
def badd(a,b):return (a[0]+b[0],a[1]+b[1])
def scale(q,a):return (q*a[0],q*a[1]) if q>=0 else (q*a[1],q*a[0])
def point(q):return (q,q)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--project',type=Path,default=Path(__file__).resolve().parents[2]);ap.add_argument('--out',type=Path);ap.add_argument('--cells',type=int,default=N,help='Diagnostic prefix only; only 50000 is a complete verification');ap.add_argument('--trans',type=Path);ap.add_argument('--grid',type=Path)
 args=ap.parse_args();p=args.project.resolve();start=time.monotonic();require(0<args.cells<=N,'cell count')
 tp=args.trans or p/'numerical/external26/transcendental_values.txt';gp=args.grid or p/'numerical/fullgrid27/grid_arithmetic.txt'
 require(sha(tp)==TRANS_SHA,'transcendental data SHA256 mismatch');require(sha(gp)==GRID_SHA,'grid data SHA256 mismatch')
 manifest=json.loads((p/'numerical/fullgrid27/source_manifest.json').read_text())
 for name,digest in manifest.items(): require(sha(p/name)==digest,'source changed: '+name)
 src=(p/'lean/FourValueCertificate.lean').read_text();centers=[tuple(Q(x) for x in row) for row in lists(src,'centers')];weights=lists(src,'weightRows');knots=[tuple(Q(x) for x in row) for row in lists(src,'knotBounds')]
 require(len(centers)==45 and len(weights)==40 and len(knots)==42,'table dimensions')
 for w in weights: require(len(w)==45 and all(type(x)==int and x>=0 for x in w) and sum(w)==10**8,'weight row')
 sparse=[[(j,v) for j,v in enumerate(w) if v] for w in weights]
 aa=[Q(x,100) for x in [67]*5+[63,60,58,57,54,52,49,47,44,42]]
 # These are the two small endpoint definitions in the pinned Lean source.
 unique=aa[4:];shifts=[Q(1),Q(-1)]+[a for x in unique for a in [x,-x]]
 constants=[2*x for x in aa[5:]]+[Q(33,100)]+[(1+x)/(1-x) for x in unique]
 tf=tp.open('rb');gf=gp.open('rb');t=mmap.mmap(tf.fileno(),0,access=mmap.ACCESS_READ);g=mmap.mmap(gf.fileno(),0,access=mmap.ACCESS_READ)
 require(len(t)==4096+58*(LC+AC) and len(g)==18*46*N,'length')
 def row(i,kind):
  r=t[4096+58*i:4096+58*(i+1)]
  require(re.fullmatch(rb'[LA] [0-9]{16} [0-9]{16} [+-][0-9]{20}\n',r) is not None,'row syntax')
  require(r[:1]==kind,'row kind');num=int(r[2:18]);den=int(r[19:35]);z=int(r[36:57]);require(den>0,'denominator')
  return Q(num,den),(Q(z,S),Q(z+5,S))
 cb=[]
 for i,q in enumerate(constants):
  got,b=row(i,b'L');require(got==q,f'constant identity {i}');cb.append(b)
 ent=point(Q(0))
 for i,a in enumerate(aa[5:]):ent=badd(ent,badd(scale(2*a,cb[i]),point(-2*a)))
 ent=badd(ent,scale(Q(-10),badd(scale(Q(33,100),cb[10]),point(Q(-33,100)))))
 slope=point(Q(0))
 for i in range(15):slope=badd(slope,cb[11 if i<5 else i+7])
 slope=scale(Q(3,50000),slope)
 pi=(Q(314159265358979323844,10**20),Q(314159265358979323864,10**20))
 min_g=None;min_pair=None;min_knot=None;arg_checks=22
 def sqdist(y,x,z):
  return (1+Q(6,5)*y-Q(16,25)*y*y-x)**2+(2*y+Q(6,5)*y*y-z)**2
 for k in range(args.cells):
  y=Q(k+1,10000);left=Q(k,10000);c=1+Q(3,5)*y
  raw=g[18*46*k:18*46*(k+1)]
  require(re.fullmatch(rb'(?:[+-][0-9]{16}\n){46}',raw) is not None,'grid syntax')
  gi=[int(raw[18*i:18*(i+1)]) for i in range(46)];G=Q(gi[0],10**8);K=gi[1:]
  jb=[]
  for slot,a in enumerate(shifts):
   u=c+a;q,lb=row(22+114*k+slot,b'L');r,ab=row(LC+24*k+slot,b'A')
   require(q==u*u+y*y and r==u/y,f'J identity {k}/{slot}');arg_checks+=2
   jb.append(badd(badd(scale(u/2,lb),point(-u)),scale(y,ab)))
  gb=badd(ent,scale(Q(5),badd(jb[0],scale(Q(-1),jb[1]))))
  total=point(Q(0))
  for i in range(15):
   slot=2 if i<5 else 2*(i-4)+2
   total=badd(total,badd(jb[slot],scale(Q(-1),jb[slot+1])))
  gb=badd(badd(gb,scale(Q(-1),total)),badd(scale(-2*y+Q(19,20000),pi),slope))
  margin=G-gb[1];require(margin>=0,f'G bound {k}');min_g=margin if min_g is None else min(min_g,margin)
  for j,(x,z) in enumerate(centers):
   q,ub=row(22+114*k+24+2*j,b'L');r,vb=row(22+114*k+25+2*j,b'L')
   U=q-Q(17,5000000000);V=r-Q(17,5000000000)
   require(U>=Q(1,50) and V>=Q(1,50),f'cutoffs {k}/{j}')
   require(sqdist(left,x,z)<=U*U and sqdist(y,x,z)<=U*U and sqdist(left,x,-z)<=V*V and sqdist(y,x,-z)<=V*V,f'distances {k}/{j}')
   margin=Q(K[j],10**8)-ub[1]-vb[1];require(margin>=0,f'pair bound {k}/{j}');min_pair=margin if min_pair is None else min(min_pair,margin)
  for m in range(42):
   knot=Q(0) if m==0 else Q(361,200) if m==41 else Q(361*(2*m-1),16000)
   require(knots[m][0]==knot,f'knot abscissa {m}')
   dot=sum(w*K[j] for j,w in sparse[min(max(m-1,0),39)])
   margin=knots[m][1]-G-knot*Q(dot,10**16)
   require(margin>=0,f'knot bound {k}/{m}');min_knot=margin if min_knot is None else min(min_knot,margin)
  if (k+1)%1000==0:print(json.dumps({'cells':k+1,'seconds':round(time.monotonic()-start,2)}),flush=True)
 result={'status':'PASS' if args.cells==N else 'PREFIX_ONLY','complete':args.cells==N,'cells':args.cells,'rational_argument_identities':arg_checks,'expression_upper_checks':args.cells,'distance_square_checks':4*45*args.cells,'distance_cutoff_checks':2*45*args.cells,'log_pair_checks':45*args.cells,'knot_checks':42*args.cells,'min_G_slack':str(min_g),'min_pair_slack':str(min_pair),'min_knot_slack':str(min_knot),'seconds':time.monotonic()-start,'grid_sha256':GRID_SHA,'transcendental_sha256':TRANS_SHA,'assumed_rational_families':5,'transcendental_claims_checked_here':False,'arithmetic':'FLINT exact fmpq and Python arbitrary precision integers'}
 out=args.out or p/'numerical/fullgrid27/verification.json';out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__': main()

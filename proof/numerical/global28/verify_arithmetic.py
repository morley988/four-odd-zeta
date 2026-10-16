"""Independent exact-rational verification of the finite arithmetic cell data.
Requires python-flint==0.9.0. No floating-point comparisons are used.
This checks finite numerical claims, not their mathematical application.
"""
if not __debug__:
 raise RuntimeError("Run without -O: assertion checks must remain enabled")

from pathlib import Path
from flint import fmpq as Q
from concurrent.futures import ProcessPoolExecutor
import hashlib,json,time,argparse
A=(100,67,63,60,58,57,54,52,49,47,44,42)
TAIL=A[2:]
def fl(x): return int(x.numerator//x.denominator)
def ce(x): return -fl(-x)
def verify(row):
 l,h,t,v=row.split();l,h,v=Q(l),Q(h),Q(v);t=int(t)
 assert Q(1,20)<=l<h<=361 and 0<=t<=20000
 cuts={Q(0),h/2}
 for a in A:
  for u in (l,h):
   r=a-fl(a/u)*u
   cuts.update(y for y in (r,u-r) if 0<y<h/2)
 cuts=sorted(cuts)
 nf=[fl(2*a/h) for a in TAIL];j=ce(33/l)-1
 assert all(k>=0 and k*h<=2*a for k,a in zip(nf,TAIL))
 assert j+1>0 and 33<=(j+1)*l
 nu=sum(nf)-10*j;total=Q(0);maxpen=0
 for yl,yh in zip(cuts,cuts[1:]):
  F={}
  for a in A:
   pp=[(a+y)/u for u in (l,h) for y in (yl,yh)]
   mm=[(a-y)/u for u in (l,h) for y in (yl,yh)]
   F[a]=(fl(min(pp)),ce(max(pp))-1,fl(min(mm)),ce(max(mm))-1)
   L,H,M,N=F[a]
   assert all(L*u<=a+y<=(H+1)*u and M*u<=a-y<=(N+1)*u for u in (l,h) for y in (yl,yh))
  low=lambda a:F[a][0]+F[a][2]+1
  high=lambda a:F[a][1]+F[a][3]+1
  cap=max(0,sum(high(a) for a in TAIL))
  lam=nu+5*low(100)-5*high(67)-sum(high(a) for a in TAIL)
  U,V=F[63][1],F[63][3]
  good=all(67-y+u*U<=u and 67+y+u*V<=u for u in (l,h) for y in (yl,yh))
  single=good and U+V<=0
  aa=lam if good else lam-5
  # Maximize t*m - max(m*m+aa*m,nu*m) on integer 0<=m<=cap.
  # Quadratic vertex, endpoints and the kink exhaust all candidates.
  vertex=(t-aa)//2
  candidates={0,cap}
  for k in (vertex,nu-aa):
   candidates.update(max(0,min(cap,k+d)) for d in (-1,0,1,2))
  def f(m):return t*m-max(m*m+aa*m,nu*m) if single else t*m-m*m-aa*m
  pen=max(f(m) for m in candidates)
  assert pen>=0
  total+=(yh-yl)*pen;maxpen=max(maxpen,pen)
 k=fl(361/l);assert l*k<=361<=l*(k+1)
 actual=Q(t*361,2)-total-(361*k-l*k*(k+1)/2)
 assert v<=actual,(str(l),str(v),str(actual))
 return fl((h-l)*v*10**8),len(cuts)-1,maxpen

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--workers',type=int,default=4);args=parser.parse_args()
 path=Path(__file__).with_name('arithmetic_cells.txt');data=path.read_bytes()
 rows=[s for s in data.decode().splitlines() if s and not s.startswith('#')]
 assert len(rows)==171504
 last=Q(1,20)
 for row in rows:
  l,h,_,_=row.split();assert Q(l)==last;last=Q(h)
 assert last==361
 start=time.monotonic();total=boxes=maxpen=0
 with ProcessPoolExecutor(max_workers=args.workers) as ex:
  for i,(s,b,m) in enumerate(ex.map(verify,rows,chunksize=200),1):
   total+=s;boxes+=b;maxpen=max(maxpen,m)
   if i%10000==0: print(json.dumps({'cells':i,'seconds':round(time.monotonic()-start,1)}),flush=True)
 integral=Q(total,10**8);assert integral>=-114800
 rate=integral/10000-Q(361,10000);assert rate>Q(-288,25)
 result=dict(passed=True,cells=len(rows),boxes_including_zero_capacity=boxes,main_integral_lower=str(integral),normalized_with_small_prime_allowance=str(rate),target_lower_rate='-288/25',maximum_box_penalty=maxpen,data_sha256=hashlib.sha256(data).hexdigest(),seconds=time.monotonic()-start,method='exact rational corner bounds and integer quadratic vertices; each integral term rounded downward at 1e-8')
 Path(__file__).with_name('verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__':main()

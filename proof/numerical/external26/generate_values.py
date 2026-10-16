"""Export exact rational arguments and proposed decimal enclosures. Not trusted."""
import argparse,hashlib,json,math,time
from pathlib import Path
from fractions import Fraction as Q
from flint import arb,ctx
SCALE=10**18; HEADER=4096; RECORD=58; N=50000

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--witness',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--cells',type=int,default=N);args=ap.parse_args()
 ctx.prec=192;start=time.monotonic();w=json.loads(args.witness.read_text());aa=list(map(Q,w['a']));unique=list(dict.fromkeys(aa));shifts=[Q(1),Q(-1)]+[x for a in unique for x in [a,-a]]
 constants=[2*a for a in aa[5:]]+[Q(33,100)]+[(1+a)/(1-a) for a in unique]
 assert len(constants)==22 and len(shifts)==24
 cells=args.cells;logs=22+114*cells;atans=24*cells
 meta={'format':'FV_TRANS_V1','header_bytes':HEADER,'record_bytes':RECORD,'scale':SCALE,'upper_minus_lower_numerator':5,'log_count':logs,'atan_count':atans,'cells':cells,'full_grid_cells':N,'generator_precision_bits':192,'columns':'kind[0], space, positive numerator[2:18], space, positive denominator[19:35], space, signed lower numerator[36:57], LF','order':'22 constant logs; 114 logs/cell (24 J logs, then 45 distance pairs); 24 arctangents/cell','constants':[str(x) for x in constants],'shifts':[str(x) for x in shifts],'meaning':'q=numerator/denominator; lower=lower_numerator/10^18; upper=(lower_numerator+5)/10^18; arctangent in radians'}
 header=(json.dumps(meta,separators=(',',':'))+'\n').encode();assert len(header)<HEADER
 args.out.parent.mkdir(parents=True,exist_ok=True);tmp=args.out.with_suffix('.atan.tmp')
 def line(kind,num,den):
  g=math.gcd(num,den);num//=g;den//=g
  assert 0<num<10**16 and 0<den<10**16
  x=arb(num)/den;v=x.log() if kind=='L' else x.atan()
  z=int((v*SCALE).floor().unique_fmpz())-2
  b=f'{kind} {num:016d} {den:016d} {z:+021d}\n'.encode();assert len(b)==RECORD
  return b
 D=25*10000**2;centers=[(int(Q(x)*D),int(Q(y)*D)) for x,y in w['centers']]
 assert all(Q(x)*D==xx and Q(y)*D==yy for (x,y),(xx,yy) in zip(w['centers'],centers))
 def distances(k):
  re=D+30*k*10000-16*k*k;im=50*k*10000+30*k*k
  def ceil(dx,dy):
   sq=(dx*dx+dy*dy)*10**20;den=D*D;n=math.isqrt(sq//den);return n+(n*n*den<sq)
  return [(ceil(re-x,im-y),ceil(re-x,im+y)) for x,y in centers]
 prev=distances(0)
 with args.out.open('wb') as f,tmp.open('wb') as aout:
  f.write(header+b' '*(HEADER-len(header)))
  for q in constants:f.write(line('L',q.numerator,q.denominator))
  for k in range(cells):
   # c=(50000+3*(k+1))/50000, y=(k+1)/10000
   t=k+1
   for shift in shifts:
    un=(50000+3*t)*shift.denominator+50000*shift.numerator;ud=50000*shift.denominator
    n=un*un*10**8+t*t*ud*ud;d=ud*ud*10**8
    f.write(line('L',n,d));aout.write(line('A',un*10000,ud*t))
   cur=distances(t)
   for old,new in zip(prev,cur):
    for sign in range(2):
     ceiling=max(old[sign],new[sign],200000000)
     f.write(line('L',ceiling+34,10**10))
   prev=cur
   if t%1000==0:print(json.dumps({'cells':t,'seconds':round(time.monotonic()-start,2)}),flush=True)
 with args.out.open('ab') as f,tmp.open('rb') as a:
  while b:=a.read(8*1024*1024):f.write(b)
 tmp.unlink();assert args.out.stat().st_size==HEADER+(logs+atans)*RECORD
 h=hashlib.file_digest(args.out.open('rb'),'sha256').hexdigest()
 result={'file':args.out.name,'sha256':h,'log_count':logs,'atan_count':atans,'rows':logs+atans,'bytes':args.out.stat().st_size,'seconds':time.monotonic()-start,'complete':cells==N}
 args.out.with_suffix('.manifest.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__':main()

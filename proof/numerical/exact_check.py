"""Independent integer-only audit of the stored analytic certificate.
No floating point or transcendental library is used for enclosure arithmetic.
See exact_check_method.txt for the directed rounding and remainder bounds.
This is a Python verifier, NOT a Lean proof or a trusted Lean oracle.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json,time,hashlib,sys
import numpy as np
if not __debug__:
 raise RuntimeError("Run without -O: all certificate assertions must be enabled")
ROOT=Path(__file__).resolve().parent
S=1<<160
N=48

def ceildiv(a,b): return -((-a)//b)
def add(a,b):return a[0]+b[0],a[1]+b[1]
def neg(a):return -a[1],-a[0]
def sub(a,b):return add(a,neg(b))
def mulq(a,q):
 q=F(q)
 if q<0:return neg(mulq(a,-q))
 return a[0]*q.numerator//q.denominator,ceildiv(a[1]*q.numerator,q.denominator)
def rational(q):
 q=F(q);return q.numerator*S//q.denominator,ceildiv(q.numerator*S,q.denominator)
def summ(xs):
 a=(0,0)
 for x in xs:a=add(a,x)
 return a

def log_unit(num,den):
 assert den<=num<=2*den
 # 0 <= t <= 1/3; all polynomial terms rounded downward.
 t=(num-den)*S//(num+den);t2=t*t//S;p=t;v=0
 for j in range(N):
  v+=p//(2*j+1);p=p*t2//S
 rem=ceildiv(18*S,8*(2*N+1)*3**(2*N+1))
 return 2*v,2*v+4*N*N+rem
LOG2=log_unit(2,1)
def logq(q):
 q=F(q);num,den=q.numerator,q.denominator
 assert num>0
 e=num.bit_length()-den.bit_length()
 if e>=0:d=den<<e;n=num
 else:d=den;n=num<<(-e)
 if n<d:e-=1;n*=2
 assert d<=n<2*d
 return add(log_unit(n,d),mulq(LOG2,e))

def atan_small(q):
 q=F(q)
 if q<0:return neg(atan_small(-q))
 assert 0<=q<=F(1,2)
 t=q.numerator*S//q.denominator;t2=t*t//S;p=t;v=0
 for j in range(72):
  term=p//(2*j+1);v+=term if j%2==0 else -term;p=p*t2//S
 error=4*72*72+ceildiv(S,145*2**145)
 return v-error,v+error
PI=sub(mulq(atan_small(F(1,5)),16),mulq(atan_small(F(1,239)),4))
def atanq(q):
 q=F(q)
 if q<0:return neg(atanq(-q))
 if q>1:return sub(mulq(PI,F(1,2)),atanq(1/q))
 if q>F(1,2):return add(mulq(PI,F(1,4)),atan_small((q-1)/(q+1)))
 return atan_small(q)

def main():
 start=time.time();w=json.load(open(ROOT/'replay/round7_basis_witness.json'))
 cert=json.load(open(ROOT/'replay/round7_real_certificate.json'))
 grid=np.load(ROOT/'replay/round7_real_grid.npz');G,K=grid['G'],grid['K']
 aa=list(map(F,w['a']));centers=[tuple(map(F,z))for z in w['centers']]
 weights=w['weights'];r=w['r'];kap=F(w['kappa']);delta=F(w['delta']);C=(sum(aa)-r)/2
 assert (r,kap,delta,C)==(5,F(3,5),F(1,50),F(361,200))
 assert len(aa)==15 and len(centers)==45 and len(weights)==40
 assert all(0<a<1 for a in aa)
 assert all(len(row)==45 and all(isinstance(t,int) and t>=0 for t in row) and sum(row)==10**8 for row in weights)
 assert G.shape==(50000,) and K.shape==(45,50000)
 entropy=lambda u:mulq(sub(logq(u),rational(1)),u)
 entropyS=sub(summ(entropy(2*a)for a in aa[r:]),mulq(summ(entropy(1-a)for a in aa[:r]),2))
 D=(r+sum(a**3 for a in aa))/3;R=max(abs(x)+abs(z)+delta for x,z in centers)
 tail=sub(add(add(entropyS,rational(D/24)),rational(2*C*R/25)),mulq(PI,10))
 assert tail[1]*F(10**8,S)<=F(cert['tail_upper'])*10**8
 L=add(mulq(summ(logq((1+a)/(1-a))for a in aa),kap),mulq(PI,F(19,2)))
 coord_den=2500000000;dist_scale=10**10;scale=10**8
 ci=[(int(x*coord_den),int(z*coord_den))for x,z in centers]
 assert all(F(x,coord_den)==a and F(y,coord_den)==b for (x,y),(a,b)in zip(ci,centers))
 def endpoints(k):
  re=25*10000**2+30*k*10000-16*k*k;im=50*k*10000+30*k*k
  result=[]
  for x,z in ci:
   row=[]
   for imag in (im-z,im+z):
    sq=((re-x)**2+imag**2)*dist_scale**2;den2=coord_den**2
    m=isqrt(sq//den2);m+=m*m*den2<sq
    assert m*m*den2>=sq and (m==0 or (m-1)**2*den2<sq)
    row.append(m)
   result.append(row)
  return result
 previous=endpoints(0);curv=F(17,5000000000)
 counts={'G_cells':0,'K_cells':0,'distance_ceilings':90}
 for k in range(1,50001):
  y=F(k,10000);c=1+kap*y
  def J(u):return add(sub(mulq(logq(u*u+y*y),u/2),rational(u)),mulq(atanq(u/y),y))
  # Evaluate repeated denominator endpoints once, but count all multiplicities.
  differences={a:sub(J(c+a),J(c-a))for a in set(aa+[F(1)])}
  g=add(sub(sub(add(entropyS,mulq(differences[F(1)],r)),summ(differences[a]for a in aa)),mulq(PI,2*y)),mulq(L,F(1,10000)))
  assert g[1]*scale<=int(G[k-1])*S,('G',k)
  current=endpoints(k);counts['distance_ceilings']+=90
  for j in range(45):
   u=max(previous[j][0],current[j][0],200000000)
   v=max(previous[j][1],current[j][1],200000000)
   bound=add(logq(F(u,dist_scale)+curv),logq(F(v,dist_scale)+curv))
   assert bound[1]*scale<=int(K[j,k-1])*S,('K',j,k)
  previous=current;counts['G_cells']+=1;counts['K_cells']+=45
  if k%5000==0:print(json.dumps(dict(cell=k,seconds=time.time()-start)),flush=True)
 # Python arbitrary-precision accumulation independently verifies all 42 maxima.
 knots=[F(0)]+[C*F(2*j+1,80)for j in range(40)]+[C]
 vals=[]
 for j,s in enumerate(knots):
  row=weights[min(max(j-1,0),39)]
  den=10**8*s.denominator
  best=None;best_i=None
  for t in range(50000):
   n=int(G[t])*den+s.numerator*sum(a*int(K[l,t])for l,a in enumerate(row)if a)
   if best is None or n>=best:best,best_i=n,t
  val=max(F(best,den*scale),F(cert['tail_upper']))
  assert val==F(cert['knots'][j]['upper'])
  assert s==F(cert['knots'][j]['s'])
  vals.append(val)
 integral=sum((b-a)*(u+v)/2 for a,b,u,v in zip(knots,knots[1:],vals,vals[1:]))
 assert integral==F(cert['integral_upper'])
 rate=add(sub(rational(integral),mulq(logq(2*C),2*C*C)),rational(3*C*C))
 assert rate[1]*F(1,S)<=F(cert['real_exponent_upper'])
 output=dict(status='all independent integer enclosure checks passed',lean_kernel_verified=False,counts=counts,knots=42,integral=str(integral),real_exponent_upper=cert['real_exponent_upper'],tail_upper=cert['tail_upper'],fixed_point_bits=160,log_terms=N,atan_terms=72,seconds=time.time()-start)
 (ROOT/'exact_check_result.json').write_text(json.dumps(output,indent=2)+'\n');print(json.dumps(output),flush=True)
if __name__=='__main__':main()

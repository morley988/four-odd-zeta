"""Arb/integer certificate for the tilted-contour, disk-polynomial real bound.
Every y-cell is enclosed; the infinite tail is bounded analytically. Root
centers and mixture weights are rationalized before certification. All final
maxima and integrations use integer/rational arithmetic.
"""
import json,time,math,gzip,hashlib
from fractions import Fraction as F
import numpy as np
from flint import arb,ctx
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def ceila(x):
 z=x.upper().ceil().unique_fmpz();assert z is not None, str(x);return int(z)
def ar(q):
 q=F(q);return arb(q.numerator)/q.denominator

def run(grid_den=10000,Ymax=5,scale=100000000,dist_scale=10000000000,weight_den=100000000):
 start=time.time();ctx.prec=128
 witness=json.loads((ROOT/'round7_basis_witness.json').read_text())
 aa=list(map(F,witness['a']));r=witness['r'];q=len(aa);beta=sum(aa)-r;C=beta/2;kap=F(witness['kappa']);delta=F(witness['delta'])
 assert kap==F(3,5)
 centers=[(F(x),F(y))for x,y in witness['centers']]
 weights=witness['weights'];weight_den=witness['weight_den']
 assert all(min(row)>=0 and sum(row)==weight_den for row in weights)

 ns=len(weights);nc=len(centers);length=Ymax*grid_den
 def ff(u):return ar(u)*(ar(u).log()-1)if u else arb(0)
 S=sum(ff(2*a)for a in aa[r:])-2*sum(ff(1-a)for a in aa[:r]);pi=arb.pi()
 M=ar(kap)*sum((ar(1+a)/ar(1-a)).log()for a in aa)+arb(q+4)*pi/2
 R=max(abs(x)+abs(y)+delta for x,y in centers);D=(r+sum(a**3 for a in aa))/3
 tail=S+ar(D)/arb(Ymax*Ymax-1)+2*ar(C)*ar(R)/(Ymax*Ymax)-2*pi*Ymax
 tail_upper=ceila(tail*scale)
 curv=(1+kap*kap)/F(4*grid_den*grid_den)
 Gvals=np.empty(length,dtype=np.int64);Kvals=np.empty((nc,length),dtype=np.int64)
 coord_den=math.lcm(25*grid_den*grid_den,1000000)
 coord_factor=coord_den//(25*grid_den*grid_den)
 assert all((x*coord_den).denominator==1 and (v*coord_den).denominator==1 for x,v in centers)
 center_ints=[(int(x*coord_den),int(v*coord_den))for x,v in centers]
 def distance_ceil(dx,dy):
  squared=(dx*dx+dy*dy)*dist_scale*dist_scale
  den2=coord_den*coord_den
  t=math.isqrt(squared//den2)
  return t+(t*t*den2<squared)
 def distances(y):
  k=int(y*grid_den);assert F(k,grid_den)==y
  re=(25*grid_den*grid_den+30*k*grid_den-16*k*k)*coord_factor
  im=(50*k*grid_den+30*k*k)*coord_factor
  return [(distance_ceil(re-x,im-v),distance_ceil(re-x,im+v))for x,v in center_ints]

 previous=distances(F(0));delta_int=math.ceil(delta*dist_scale)
 for k in range(1,length+1):
  y=arb(k)/grid_den;c=1+ar(kap)*y
  def J(u):return u*((u*u+y*y).log()/2-1)+y*(u/y).atan()
  G=S+r*(J(c+1)-J(c-1))-sum(J(c+ar(a))-J(c-ar(a))for a in aa)-2*pi*y+M/grid_den
  Gvals[k-1]=ceila(G*scale);current=distances(F(k,grid_den))
  for j in range(nc):
   u=max(previous[j][0],current[j][0],delta_int);v=max(previous[j][1],current[j][1],delta_int)
   Kvals[j,k-1]=ceila(((arb(u)/dist_scale+ar(curv)).log()+(arb(v)/dist_scale+ar(curv)).log())*scale)
  previous=current
  if k%5000==0:print(json.dumps(dict(stage='Arb cell bounds',cell=k,total=length,seconds=time.time()-start)),flush=True)
 # The integer dot product is safe: positive weights sum to weight_den.
 assert max(abs(int(Kvals.min())),abs(int(Kvals.max())))*weight_den<2**63
 WG=np.asarray(weights,dtype=np.int64)@Kvals
 knot_s=[F(0)]+[C*F(2*j+1,2*ns)for j in range(ns)]+[C]
 values=[];witnesses=[]
 for j,s in enumerate(knot_s):
  if s==0:
   i=int(np.argmax(Gvals));v=F(max(int(Gvals[i]),tail_upper),scale)
  else:
   row=min(j-1,ns-1);den=weight_den*s.denominator
   num,i=max((int(Gvals[t])*den+s.numerator*int(WG[row,t]),t)for t in range(length))
   v=max(F(num,den*scale),F(tail_upper,scale))
  values.append(v);witnesses.append(dict(s=str(s),upper=str(v),cell_index=i))
 integral=sum((b-a)*(u+v)/2 for a,b,u,v in zip(knot_s,knot_s[1:],values,values[1:]))
 constant=-2*ar(C)**2*(2*ar(C)).log()+3*ar(C)**2
 A=ar(integral)+constant;upper=F(ceila(A*scale),scale)
 np.savez_compressed(ROOT/'round7_real_grid.npz',G=Gvals,K=Kvals)
 out=dict(complete=True,B=100,a=[str(a)for a in aa],r=r,q=q,beta=str(beta),C=str(C),kappa=str(kap),delta=str(delta),centers=[[str(x),str(y)]for x,y in centers],weights=weights,weight_den=weight_den,grid_den=grid_den,Ymax=Ymax,scale=scale,dist_scale=dist_scale,precision_bits=ctx.prec,derivative_lower_bound_magnitude=M.str(35),root_modulus_bound=str(R),tail_upper=str(F(tail_upper,scale)),integral_upper=str(integral),real_exponent_upper=str(upper),decimal_real_upper=float(upper),knots=witnesses,grid_sha256=hashlib.sha256((ROOT/'round7_real_grid.npz').read_bytes()).hexdigest(),seconds=time.time()-start,status='Certified numerical upper bound; depends on the contour deformation, bounded-root basis transfer and asymptotic lemmas stated in the proof note.')
 (ROOT/'round7_real_certificate.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items()if k not in ['centers','weights','knots']}),flush=True)
if __name__=='__main__':run()

"""Exact verification of the balanced part of the frozen d=6 two-bend certificate.
Raw pair bases are averaged symmetric/alternating tensors of factorial-Fock monomials.
All operators, Casimir interpolation, highest-weight bases and pivots are rational.
"""
import itertools as it,math,json,sys,time,hashlib
from pathlib import Path
from collections import defaultdict,Counter
from fractions import Fraction as F
import numpy as np
import scipy.sparse as sp
from flint import fmpq_mat as Mat,fmpq
ROOT=Path(__file__).resolve().parent
COEFF=ROOT/'rational38_d6.json'
if not COEFF.exists():COEFF=ROOT.parent/'sl4_full_search/rational38_d6.json'

def comps(n,d):
 if d==1:return [(n,)]
 return [(i,)+a for i in range(n+1)for a in comps(n-i,d-1)]
def mf(a):return math.prod(math.factorial(int(v))for v in a)
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def shift(w,a,b):
 v=list(w);v[a]+=1;v[b]-=1;return tuple(v)
def ctype(p):
 seen=set();out=[]
 for i in range(4):
  if i in seen:continue
  j=i;n=0
  while j not in seen:seen.add(j);n+=1;j=p[j]
  out.append(n)
 return tuple(sorted(out,reverse=True))
PERMS=list(it.permutations(range(4)));CLASSES=[(1,1,1,1),(2,1,1),(2,2),(3,1),(4,)];CHARS=[[1,1,1,1,1],[3,1,-1,0,-1],[3,-1,-1,0,1],[2,0,2,-1,0]]
def q(x):return fmpq(str(x))
def mat(a):return Mat([[int(x)for x in row]for row in a])
def eye(n):return mat(np.eye(n,dtype=np.int64))
def serialize(A):return [[str(A[i,j])for j in range(A.ncols())]for i in range(A.nrows())]
def deserialize(A):return Mat([[q(x)for x in row]for row in A])
def nullspace(K):
 if K.shape[0]==0:return eye(K.shape[1])
 A,r=mat(K).rref();cols=A.ncols();piv=[]
 for i in range(r):piv.append(next(j for j in range(cols)if A[i,j]))
 frees=[j for j in range(cols)if j not in piv];out=[]
 for f in frees:
  v=[fmpq(0)for _ in range(cols)];v[f]=fmpq(1)
  for i,p in enumerate(piv):v[p]=-A[i,f]
  den=math.lcm(*[int(z.denominator)for z in v]);w=[int(z*den)for z in v];g=math.gcd(*w);out.append([z//g for z in w])
 return mat(np.array(out,dtype=np.int64).T)if out else Mat(cols,0)
def psd(H):
 n=H.nrows();A=Mat(H);piv=[]
 for i in range(n):
  p=A[i,i];piv.append(str(p))
  if p<0:return False,piv
  if not p:
   if any(A[i,j]for j in range(i+1,n)):return False,piv
   continue
  for j in range(i+1,n):
   if not A[j,i]:continue
   v=A[j,i]/p
   for k in range(j,n):A[j,k]-=v*A[i,k];A[k,j]=A[j,k]
 return True,piv

def poly_coeff(xs,ys):
 out=[F(0)]*len(xs)
 for j,(x,y)in enumerate(zip(xs,ys)):
  p=[F(y)];den=1
  for k,z in enumerate(xs):
   if j==k:continue
   p=[F(0)]+p
   for i in range(len(p)-1):p[i]-=z*p[i+1]
   den*=x-z
  for i,v in enumerate(p):out[i]+=v/den
 return [q(x)for x in out]
def polyapply(C,B,xs,ys):
 co=poly_coeff(xs,ys);A=co[-1]*B
 for v in reversed(co[:-1]):A=C*A+v*B
 return A

class Sector:
 def __init__(self,d,s,t):
  assert d==6, 'This certificate and its cubic Casimir constants are for d=6.'
  self.d=d;self.s=s;self.t=t;self.bs=comps(2,d);self.bl={a:i for i,a in enumerate(self.bs)};self.n=len(self.bs)
  self.L=self.pair(s);self.R=self.pair(t);self.pure=defaultdict(list);self.mixed=defaultdict(list)
  for i,j in it.product(range(len(self.L['pairs'])),range(len(self.R['pairs']))):
   self.pure[add(self.L['sum'][i],self.R['sum'][j])].append((i,j));self.mixed[sub(self.L['sum'][i],self.R['sum'][j])].append((i,j))
  self.pidx={w:{p:i for i,p in enumerate(v)}for w,v in self.pure.items()};self.transcache={};self.canonmap={};self.canon={}
  self.coeff=[F(x)for x in json.loads(COEFF.read_text())['coefficients']]
  self.digest=hashlib.sha256(json.dumps([str(x)for x in self.coeff]).encode()).hexdigest()
 def pair(self,sign):
  pairs=list(it.combinations_with_replacement(range(self.n),2))if sign==1 else list(it.combinations(range(self.n),2));idx={p:i for i,p in enumerate(pairs)}
  orb=[1 if a==b else 2 for a,b in pairs];pw=[mf(self.bs[a])*mf(self.bs[b])for a,b in pairs];g=[F(v,o)for v,o in zip(pw,orb)];sums=[add(self.bs[a],self.bs[b])for a,b in pairs];acts={}
  for a,b in it.product(range(self.d),repeat=2):
   acts[a,b]=[]
   for src in pairs:
    out=defaultdict(int)
    for r in range(2):
     al=self.bs[src[r]]
     if not al[b]:continue
     be=list(al);be[a]+=1;be[b]-=1;dest=list(src);dest[r]=self.bl[tuple(be)]
     if sign==-1 and dest[0]==dest[1]:continue
     sg=sign if dest[0]>dest[1]else 1;row=idx[tuple(sorted(dest))];out[row]+=sg*al[b]
    acts[a,b].append(list(out.items()))
  return {'pairs':pairs,'idx':idx,'orb':orb,'pw':pw,'g':g,'sum':sums,'act':acts,'sign':sign}
 def transition(self,a,b,w):
  key=(a,b,w)
  if key in self.transcache:return self.transcache[key]
  dest=shift(w,a,b);cols=self.pure.get(w,[]);rows=self.pure.get(dest,[]);ix=self.pidx.get(dest,{})
  rr=[];cc=[];vals=[]
  for col,(i,j)in enumerate(cols):
   for ii,v in self.L['act'][a,b][i]:rr.append(ix[ii,j]);cc.append(col);vals.append(v)
   for jj,v in self.R['act'][a,b][j]:rr.append(ix[i,jj]);cc.append(col);vals.append(v)
  A=sp.csr_matrix((vals,(rr,cc)),shape=(len(rows),len(cols)),dtype=np.int64);self.transcache[key]=A;return A
 def cas(self,w,cubic=False):
  size=len(self.pure[w]);C=sp.csr_matrix((size,size),dtype=np.int64)
  if not cubic:
   for a,b in it.product(range(self.d),repeat=2):C+=self.transition(a,b,shift(w,b,a))@self.transition(b,a,w)
  else:
   for a,b,c in it.product(range(self.d),repeat=3):
    w1=shift(w,c,a);w2=shift(w,b,a)
    C+=self.transition(a,b,w2)@self.transition(b,c,w1)@self.transition(c,a,w)
  return mat(C.toarray())
 def canonical(self,w):
  path=ROOT/f'canon_{self.d}_{self.s}_{self.t}_{"_".join(map(str,w))}.json'
  if path.exists():
   old=json.loads(path.read_text())
   if old.get('coefficient_digest')==self.digest:return deserialize(old['gram'])
  t0=time.time();inds=self.pure[w];il=self.pidx[w];n=len(inds);I=eye(n);C=self.cas(w)-8*self.d*I
  Znum=np.zeros((4,n,n),dtype=np.int64);tau=np.zeros((n,n),dtype=np.int64)
  L,R=self.L,self.R;s,t=self.s,self.t
  for col,(i,j)in enumerate(inds):
   a,b=L['pairs'][i];c,e=R['pairs'][j];terms=[((a,b,c,e),1)]
   if a!=b:terms.append(((b,a,c,e),s))
   if c!=e:terms += [((x[0],x[1],e,c),amp*t)for x,amp in terms.copy()]
   den=L['orb'][i]*R['orb'][j]
   for perm in PERMS:
    cl=CLASSES.index(ctype(perm))
    for word,amp in terms:
     z=[word[p]for p in perm];sg=amp
     if s==-1 and z[0]==z[1]or t==-1 and z[2]==z[3]:continue
     if z[0]>z[1]:sg*=s
     if z[2]>z[3]:sg*=t
     ii=L['idx'][tuple(sorted(z[:2]))];jj=R['idx'][tuple(sorted(z[2:]))];row=il[ii,jj]
     for k,ch in enumerate(CHARS):Znum[k,row,col]+=ch[0]*ch[cl]*sg*(4//den)
   if s==t:tau[il[j,i],col]=1
  Z=[mat(z)/96 for z in Znum];T=mat(tau);zero=Mat(n,n);Q=Mat(n,n);x=self.coeff
  if s==t==1:
   X=[[q(F(mf(w),1)/L['g'][i]/R['g'][j])for k,l in inds]for i,j in inds];Q=Mat(X)-24*Z[0]
   pp=np.zeros((n,n),dtype=np.int64);qq=np.zeros_like(pp)
   for a,(i,j)in enumerate(inds):
    for b,(k,l)in enumerate(inds):
     if L['sum'][i]!=L['sum'][k]:continue
     p1=F(mf(L['sum'][i]),1)/L['g'][i];p2=F(mf(R['sum'][j]),1)/R['g'][j];assert p1.denominator==p2.denominator==1
     pp[a,b]=int(p1*p2);qq[a,b]=int(((6 if i==k else 0)-p1)*((6 if j==l else 0)-p2))
   pp=mat(pp)/36;qq=mat(qq)/36;Dpp=2*Z[0]*pp*Z[0]-pp*Z[0]-Z[0]*pp;Dqq=2*Z[0]*qq*Z[0]-qq*Z[0]-Z[0]*qq
   Q+=polyapply(C,Dpp,[28,16],x[:2]);Q+=q(x[2])/12*(16*Dqq-C*Dqq)
  B31=Z[1]*(I-T)if s==t==1 else(-Z[1]if s!=t else zero)
  Q+=polyapply(C,B31,[40,28,20,14,8,4,-8],x[3:10])
  B211=Z[2]*(I-T)if s==t==-1 else(-Z[2]if s!=t else zero)
  if B211!=zero:
   vals=x[10:14]+[x[15]];Q+=polyapply(C,B211,[24,20,14,8,0],vals)
   W=polyapply(C,B211,[24,20,14,8,0],[0,0,0,0,1]);C3=self.cas(w,True)
   Q+=q(x[14]-x[15])/48*(C3*W-296*W)
  B22=Z[3]*(I+T)/2*(1 if s==1 else -1)if s==t else zero
  Q+=polyapply(C,B22,[28,14,16,4,-4],x[16:21])
  if s!=t:
   mp=np.zeros((n,n),dtype=np.int64)
   for a,(i,j)in enumerate(inds):
    for b,(k,l)in enumerate(inds):
     if j==l and L['sum'][i]==L['sum'][k]:mp[a,b]=int(F(mf(L['sum'][i]),1)/L['g'][i])
   MP=mat(mp)/6;B=Z[1]*MP*Z[2]+Z[2]*MP*Z[1];Q+=polyapply(C,B,[20,14,8],x[21:24])
  Q+=polyapply(C,Z[0],[56,28,16,4,-16],[-x[24],-x[26]-x[34],-x[29],-x[31]-x[35],-x[33]])
  Q+=polyapply(C,Z[1],[40,28,20,14,8,4,-8],[-x[j]/3 for j in [25,26,27,28,30,31,32]])
  G=[q(L['g'][i]*R['g'][j])for i,j in inds]
  for i in range(n):
   for j in range(n):Q[i,j]*=G[i]
  assert Q==Q.transpose(),(w,'notselfadjoint')
  path.write_text(json.dumps({'weight':w,'indices':inds,'coefficient_digest':self.digest,'gram':serialize(Q)}))
  print('canonical',s,t,w,n,'seconds',round(time.time()-t0,2),flush=True)
  return Q
 def canonical_entry(self,u,v):
  wt=add(self.L['sum'][u[0]],self.R['sum'][u[1]])
  if wt not in self.canonmap:
   perm=tuple(sorted(range(self.d),key=lambda i:(-wt[i],i)));cw=tuple(wt[i]for i in perm)
   bmap={i:self.bl[tuple(a[j]for j in perm)]for i,a in enumerate(self.bs)}
   lm=[];rm=[]
   for P,arr in [(self.L,lm),(self.R,rm)]:
    for a,b in P['pairs']:
     aa,bb=bmap[a],bmap[b];sg=P['sign']if aa>bb else 1;arr.append((P['idx'][tuple(sorted((aa,bb)))],sg))
   ix=self.pidx[cw];mapping={}
   for a,b in self.pure[wt]:
    aa,sa=lm[a];bb,sb=rm[b];mapping[a,b]=(ix[aa,bb],sa*sb)
   self.canonmap[wt]=(cw,mapping)
  cw,mp=self.canonmap[wt]
  if cw not in self.canon:self.canon[cw]=self.canonical(cw)
  a,s=mp[u];b,t=mp[v];return s*t*self.canon[cw][a,b]
 def verify(self):
  result=[];total=0;ranktotal=0;t0=time.time()
  for wt,inds in self.mixed.items():
   if any(wt[i]<wt[i+1]for i in range(self.d-1)):continue
   blocks=[]
   for a in range(self.d-1):
    dest=self.mixed.get(shift(wt,a,a+1),[]);ix={ij:i for i,ij in enumerate(dest)};M=np.zeros((len(dest),len(inds)),dtype=np.int64)
    for col,(i,j)in enumerate(inds):
     for ii,v in self.L['act'][a,a+1][i]:M[ix[ii,j],col]+=v
     for jj,v in self.R['act'][a+1,a][j]:M[ix[i,jj],col]-=v
    blocks.append(M)
   N=nullspace(np.vstack(blocks));m=N.ncols()
   if not m:continue
   M=Mat(len(inds),len(inds))
   for a,(i,j)in enumerate(inds):
    for b,(k,l)in enumerate(inds):M[a,b]=self.canonical_entry((i,l),(k,j))
   H=N.transpose()*M*N;gg=[q(self.L['g'][i]*self.R['g'][j])for i,j in inds];GN=Mat(N)
   for i in range(N.nrows()):
    for j in range(m):GN[i,j]*=gg[i]
   G=N.transpose()*GN;ok,piv=psd(H);dim=math.prod(F(wt[i]-wt[j]+j-i,j-i)for i in range(self.d)for j in range(i+1,self.d));assert dim.denominator==1
   total+=int(dim)*m;ranktotal+=int(dim)*sum(q(p)!=0 for p in piv)
   print('HW',self.s,self.t,wt,'mult',m,'dim',dim,'PSD',ok,'pivots',piv,'elapsed',round(time.time()-t0,1),flush=True)
   result.append({'weight':wt,'dimension':int(dim),'multiplicity':m,'indices':inds,'basis':serialize(N),'H':serialize(H),'G':serialize(G),'pivots':piv,'psd':ok})
   (ROOT/f'balanced_{self.s}_{self.t}.json').write_text(json.dumps({'d':self.d,'s':self.s,'t':self.t,'coefficient_file':COEFF.name,'coefficient_digest':self.digest,'coefficients':[str(x)for x in self.coeff],'blocks':result,'dimension_so_far':total,'rank_so_far':ranktotal},indent=2))
   if not ok:raise RuntimeError(('PSD failed',wt,piv))
  assert total==len(self.L['pairs'])*len(self.R['pairs']),(total,len(self.L['pairs']),len(self.R['pairs']))
  print('COMPLETE EXACT PSD',self.s,self.t,'dimension',total,'rank',ranktotal,'seconds',round(time.time()-t0,1),flush=True)

if __name__=='__main__':
 s=int(sys.argv[1])if len(sys.argv)>1 else 1;t=int(sys.argv[2])if len(sys.argv)>2 else 1
 Sector(6,s,t).verify()

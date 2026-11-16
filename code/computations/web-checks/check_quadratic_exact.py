"""Exact rational checks for the dimension-four graphical certificate.
Symmetric occupation coordinates; all adjoints include their diagonal metrics.
Independent of determinant tensors and the dimension-three tree.
"""
from itertools import product,permutations
from math import factorial
import sympy as S
D=4

def comps(n):
 def go(n,k):
  if k==1: yield (n,); return
  for j in range(n+1):
   for t in go(n-j,k-1): yield (j,)+t
 return list(go(n,D))
def orbit(t):
 z=factorial(sum(t))
 for a in t:z//=factorial(a)
 return z
def gram(p,dual=False):return [S.Rational(1,orbit(t)) if dual else orbit(t) for t in comps(p)]
def tg(*gs):return [S.prod(x) for x in product(*gs)]
def eye(n):return S.eye(n,cls=S.SparseMatrix)
def zero(n,m):return S.zeros(n,m,cls=S.SparseMatrix)
def diag(g):return S.diag(*g,cls=S.SparseMatrix)
def dag(M,gd,gc):return diag([1/S.Rational(x) for x in gd])*M.T*diag(gc)
def kron(A,B):return S.SparseMatrix(S.kronecker_product(A,B))
def check(name,A,B):
 assert not (A-B).todok(),name
 print('PASS:',name,flush=True)
def inc(p,q):
 cp,cq,ct=comps(p),comps(q),comps(p+q);ix={v:i for i,v in enumerate(ct)}
 z=zero(len(cp)*len(cq),len(ct))
 for i,a in enumerate(cp):
  for j,b in enumerate(cq):z[i*len(cq)+j,ix[tuple(x+y for x,y in zip(a,b))]]=1
 return z
def cap(p,q):
 cp,cq,ap,bq=comps(p),comps(q),comps(p-1),comps(q-1);ai={x:i for i,x in enumerate(ap)};bi={x:i for i,x in enumerate(bq)}
 z=zero(len(ap)*len(bq),len(cp)*len(cq))
 for i,a in enumerate(cp):
  for j,b in enumerate(cq):
   for r in range(D):
    if a[r] and b[r]:
     aa=list(a);bb=list(b);aa[r]-=1;bb[r]-=1
     z[ai[tuple(aa)]*len(bq)+bi[tuple(bb)],i*len(cq)+j]+=S.Rational(orbit(bb),orbit(b))
 return z
K=comps(2);k=len(K);I=eye(k);gK=gram(2);gV=gram(1);gdV=gram(1,True);gdK=gram(2,True)
g22=tg(gK,gK);gM=tg(gK,gK,gdK);gO=tg(gK,gV,gdV);gB=tg(gram(3),gdV)
j=inc(2,1);jd=dag(j,gram(3),tg(gK,gV));s=kron(j,eye(D));sd=kron(jd,eye(D))
Ps=s*sd;Ph=eye(k*D*D)-Ps
inc4=inc(2,2);dec4=dag(inc4,gram(4),g22);Pi2=inc4*dec4;Pi=kron(Pi2,I)
swap=zero(k*k,k*k)
for a,b in product(range(k),repeat=2):swap[b*k+a,a*k+b]=1
f2=(eye(k*k)+swap)/2;f=kron(f2,I)
C11=cap(1,1);C22=cap(2,2);C31=cap(3,1);C42=cap(4,2);Cf=C11*C22
A=kron(I,C22)*f;B=C42*kron(dec4,I);C=Ph*A
u=kron(I,Cf)*f;v=kron(I,Cf)*Pi
D0=kron(I,C11);Ls=sd*dag(D0,gO,gK);Lh=Ph*dag(D0,gO,gK)
check('symmetrize the three surviving strands',sd*A,B)
check('symmetric cup bubble',dag(Ls,gK,gB)*Ls,2*I)
check('hook cup bubble',dag(Lh,gK,gO)*Lh,2*I)
check('symmetric trace path',dag(Ls,gK,gB)*B,v)
check('hook trace path',dag(Lh,gK,gO)*C,u-v)
B0=B-Ls*v/2;C0=C-Lh*(u-v)/2
check('symmetric trace-free path',dag(Ls,gK,gB)*B0,zero(k,k**3))
check('hook trace-free path',dag(Lh,gK,gO)*C0,zero(k,k**3))
def sq(T,gt):return dag(T,gM,gt)*T
P=8*sq(A,gO)+48*sq(B,gB)-2*sq(u,gK)-3*(dag(u,gM,gK)*v+dag(v,gM,gK)*u)+36*sq(v,gK)
w=u-S.Rational(7,2)*v
rhs=56*sq(B0,gB)+8*sq(C0,gO)+2*sq(w,gK)+S.Rational(87,2)*sq(v,gK)
check('full four-square identity',P,rhs)
# Check directly against the partially transposed corrected packet operator.
Pip=kron(I,Pi2);g=kron(I,f2);R=(4*f*g*f-f)/3
K3=list(product(K,repeat=3));gg=tg(gK,gK,gK)
total=[tuple(sum(t[j][r] for j in range(3)) for r in range(D)) for t in K3]
E=zero(k**3,k**3);groups={}
for i,t in enumerate(total):groups.setdefault(t,[]).append(i)
for t,indices in groups.items():
 for i in indices:
  for j in indices:E[i,j]=S.Rational(gg[j],orbit(t))
N=2*f*Pip*f-Pi*g*f-f*g*Pi;Q=90*E-6*R+6*N
Qb=zero(k**3,k**3)
for (i,j),z in Q.todok().items():
 a,b=divmod(i,k);c,d=divmod(j,k);Qb[a*k+d,c*k+b]=z
check('direct bend of Q',P,Qb)
av=zero(k**3,k**3)
for perm in permutations(range(3)):
 pp=[]
 for t in product(range(k),repeat=3):
  q=tuple(t[i] for i in perm);pp.append((q[0]*k+q[1])*k+q[2])
 av+=N.extract(pp,pp)/6
check('zero packet average',av,zero(k**3,k**3))
print('All exact over Q in dimension four.',flush=True)

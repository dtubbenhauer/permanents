from itertools import product, permutations
from math import factorial, comb
import sympy as S
D=2
def comps(n):
    return [t for t in product(range(n + 1), repeat=D) if sum(t) == n]

def orbit(t):
    z = factorial(sum(t))
    for x in t:
        z //= factorial(x)
    return z

def diag(vals):
    return S.diag(*vals)

def gram(p, dual=False):
    return [S.Rational(1, orbit(t)) if dual else orbit(t) for t in comps(p)]

def dagger(M, gd, gc):
    return diag([1 / S.Rational(x) for x in gd]) * M.T * diag(gc)

def tensorgram(*gs):
    return [S.prod(v) for v in product(*gs)]

def eye(n):
    return S.eye(n)

def zeros(n, m):
    return S.zeros(n, m)

def inclusion(p, q):
    cp, cq, ct = (comps(p), comps(q), comps(p + q))
    z = zeros(len(cp) * len(cq), len(ct))
    ix = {v: i for i, v in enumerate(ct)}
    for i, a in enumerate(cp):
        for j, b in enumerate(cq):
            z[i * len(cq) + j, ix[tuple((x + y for x, y in zip(a, b)))]] = 1
    return z

def bend_last(A, nleft, nright):
    B = zeros(nleft * nright, nleft * nright)
    for a, b, c, d in product(range(nleft), range(nright), range(nleft), range(nright)):
        B[a * nright + d, c * nright + b] = A[a * nright + b, c * nright + d]
    return B

def cap(p, q):
    cp, cq, ap, bq = (comps(p), comps(q), comps(p - 1), comps(q - 1))
    ai = {x: i for i, x in enumerate(ap)}
    bi = {x: i for i, x in enumerate(bq)}
    z = zeros(len(ap) * len(bq), len(cp) * len(cq))
    for i, a in enumerate(cp):
        for j, b in enumerate(cq):
            for r in range(D):
                if a[r] and b[r]:
                    aa = list(a)
                    bb = list(b)
                    aa[r] -= 1
                    bb[r] -= 1
                    aa = tuple(aa)
                    bb = tuple(bb)
                    z[ai[aa] * len(bq) + bi[bb], i * len(cq) + j] += S.Rational(orbit(bb), orbit(b))
    return z

def check(name,A,B):
 assert not any(A-B),name
 print('PASS:',name,flush=True)
def g(p,q):return tensorgram(gram(p),gram(q,True))
def cr(p,q,r):
 R=eye(len(g(p,q)))
 for j in range(r):R=cap(p-j,q-j)*R
 return R
def rise(x,r):return S.prod(x+j for j in range(r))
def fall(x,r):return S.prod(x-j for j in range(r))
def H(p,q):
 ret=zeros(len(g(p,q)),len(g(p,q)))
 for r in range(min(p,q)+1):
  C=cr(p,q,r)
  ret+=S.Rational((-1)**r*fall(p,r)*fall(q,r),factorial(r)*fall(D+p+q-2,r))*dagger(C,g(p,q),g(p-r,q-r))*C
 return ret
def b(p,q,r):return S.Rational((comb(D+p+q-1,r)-1)*fall(p,r)*fall(q,r),factorial(r)*rise(D+p+q-2*r,r))
for p,q in [(3,3),(6,3)]:
 inc=inclusion(p,q);pp=inc*dagger(inc,gram(p+q),tensorgram(gram(p),gram(q)))
 N=comb(p+q,p)*bend_last(pp,len(comps(p)),len(comps(q)))
 rhs=eye(len(g(p,q)))
 for r in range(1,q+1):
  T=H(p-r,q-r)*cr(p,q,r)
  rhs+=b(p,q,r)*dagger(T,g(p,q),g(p-r,q-r))*T
 check(f'cap resolution p={p},q={q},d={D}',N,rhs)
k=3;K=comps(k);nK=len(K);I=eye(nK);gKK=tensorgram(gram(k),gram(k));g3=tensorgram(gram(k),gram(k),gram(k));gM=tensorgram(gram(k),gram(k),gram(k,True))
inc=inclusion(k,k);dec=dagger(inc,gram(2*k),gKK);pi=inc*dec
swap=zeros(nK*nK,nK*nK)
for i,j in product(range(nK),repeat=2):swap[j*nK+i,i*nK+j]=1
f2=(eye(nK*nK)+swap)/2;f=S.kronecker_product(f2,I);fg=S.kronecker_product(I,f2)
Pi=S.kronecker_product(pi,I);Pip=S.kronecker_product(I,pi)
R=(4*f*fg*f-f)/3
K3=list(product(K,repeat=3));total=[tuple(sum(v[i] for v in t) for i in range(D)) for t in K3]
E=zeros(nK**3,nK**3)
for i,j in product(range(nK**3),repeat=2):
 if total[i]==total[j]:E[i,j]=S.Rational(g3[j],orbit(total[j]))
a=comb(2*k,k);c=factorial(3*k)//factorial(k)**3
Q=c*E-6*R+a*(2*f*Pip*f-Pi*fg*f-f*fg*Pi)
P=bend_last(Q,nK*nK,nK)
rhs=zeros(nK**3,nK**3)
for r in range(1,k):
 A=S.kronecker_product(I,H(k-r,k-r)*cr(k,k,r))*f
 B=H(2*k-r,k-r)*cr(2*k,k,r)*S.kronecker_product(dec,I)
 ga=tensorgram(gram(k),gram(k-r),gram(k-r,True));gb=g(2*k-r,k-r)
 rhs+=2*b(k,k,r)*dagger(A,gM,ga)*A+a*b(2*k,k,r)*dagger(B,gM,gb)*B
U=S.kronecker_product(I,cr(k,k,k))*f
V=cr(2*k,k,k)*S.kronecker_product(dec,I)
n=comb(D+k-1,k);l=comb(D+2*k-1,k);L=comb(D+3*k-1,k)
alpha=S.Rational(2*(l-1),n)-4;eta=S.Rational(a*a*(L-1),l)
W=U-S.Rational(a,2)/alpha*V
rhs+=alpha*dagger(W,gM,gram(k))*W+(eta-S.Rational(a*a,4)/alpha)*dagger(V,gM,gram(k))*V
check('full general-degree identity k=3,d=2',P,rhs)

"""Exact audits of the local symmetric-web identities and harmonic clasps.

Unnormalized monomials carry their factorial Fock metric. No diagram
multiplication table, representation-theory decomposition, or numerical
spectral computation is used in these tests.
"""
from fractions import Fraction as F
import itertools as it
import math
import numpy as np

def powers(d,n):
    if d==1:return [(n,)]
    return [(i,)+a for i in range(n+1) for a in powers(d-1,n-i)]

def basis(d,p,q):return list(it.product(powers(d,p),powers(d,q)))

def factorial(a):return math.prod(math.factorial(x) for x in a)

def metric(d,p,q):return np.array([factorial(a)*factorial(b) for a,b in basis(d,p,q)],dtype=object)

def contraction(d,p,q):
    src=basis(d,p,q);dst=basis(d,p-1,q-1);index={x:i for i,x in enumerate(dst)}
    D=np.zeros((len(dst),len(src)),dtype=object)
    for j,(a,b) in enumerate(src):
        for i in range(d):
            if not a[i] or not b[i]:continue
            aa=list(a);bb=list(b);aa[i]-=1;bb[i]-=1
            D[index[tuple(aa),tuple(bb)],j]+=a[i]*b[i]
    return D

def cup(d,p,q):
    src=basis(d,p,q);dst=basis(d,p+1,q+1);index={x:i for i,x in enumerate(dst)}
    M=np.zeros((len(dst),len(src)),dtype=object)
    for j,(a,b) in enumerate(src):
        for i in range(d):
            aa=list(a);bb=list(b);aa[i]+=1;bb[i]+=1
            M[index[tuple(aa),tuple(bb)],j]+=1
    return M

def down(d,p,q,r):
    D=np.eye(len(basis(d,p,q)),dtype=object)
    for s in range(r):D=contraction(d,p-s,q-s)@D
    return D

def up(d,p,q,r):
    M=np.eye(len(basis(d,p,q)),dtype=object)
    for s in range(r):M=cup(d,p+s,q+s)@M
    return M

def falling(a,r):return math.prod(a-j for j in range(r))
def rising(a,r):return math.prod(a+j for j in range(r))

def harmonic(d,p,q):
    n=len(basis(d,p,q));H=np.eye(n,dtype=object)
    for s in range(1,min(p,q)+1):
        coefficient=F((-1)**s,math.factorial(s)*falling(d+p+q-2,s))
        H+=coefficient*(up(d,p-s,q-s,s)@down(d,p,q,s))
    return H

def verify_clasps(d,p,q):
    n=len(basis(d,p,q));I=np.eye(n,dtype=object)
    M=cup(d,p,q);D=contraction(d,p+1,q+1)
    MD=(cup(d,p-1,q-1)@contraction(d,p,q)) if p and q else np.zeros_like(I)
    assert np.array_equal(D@M-MD,(d+p+q)*I)
    H=harmonic(d,p,q)
    assert np.array_equal(H@H,H)
    if p and q:assert not np.any(contraction(d,p,q)@H)
    g=metric(d,p,q);assert np.array_equal(g[:,None]*H,(g[:,None]*H).T)
    channels=[]
    for r in range(min(p,q)+1):
        lower=harmonic(d,p-r,q-r)
        N=math.factorial(r)*rising(d+p+q-2*r,r)
        E=F(1,N)*(up(d,p-r,q-r,r)@lower@down(d,p,q,r))
        assert np.array_equal(E@E,E)
        for other in channels:assert not np.any(E@other)
        channels.append(E)
    assert np.array_equal(sum(channels),I)
    normal=np.zeros((n,n),dtype=object)
    for r in range(min(p,q)+1):
        normal+=F(1,math.factorial(r)**2)*(up(d,p-r,q-r,r)@down(d,p,q,r))
    spectral=sum(math.comb(d+p+q-1,r)*E for r,E in enumerate(channels))
    assert np.array_equal(normal,spectral)
    # Independent multiplication / partial-transpose matrix in the Fock metric.
    src=basis(d,p,q);target=np.zeros((n,n),dtype=object)
    for i,(a,b) in enumerate(src):
        for j,(c,e) in enumerate(src):
            if tuple(x+y for x,y in zip(a,e))==tuple(x+y for x,y in zip(c,b)):
                target[i,j]=factorial(tuple(x+y for x,y in zip(a,e)))
    assert np.array_equal(g[:,None]*normal,target)
    print('web clasp',dict(d=d,p=p,q=q,dimension=n),'cup slide, clasp, orthogonal channels and bent fusion: EXACT PASS',flush=True)

def transfer(d,p,q):
    src=basis(d,p,q);dst=basis(d,p+1,q-1);index={x:i for i,x in enumerate(dst)}
    E=np.zeros((len(dst),len(src)),dtype=object)
    for j,(a,b) in enumerate(src):
        for i in range(d):
            if not b[i]:continue
            aa=list(a);bb=list(b);aa[i]+=1;bb[i]-=1
            E[index[tuple(aa),tuple(bb)],j]+=b[i]
    return E

def verify_exchange(d,k):
    src=basis(d,k,k);n=len(src);g=metric(d,k,k)
    index={s:i for i,s in enumerate(src)}
    flip=np.zeros((n,n),dtype=object)
    for j,(a,b) in enumerate(src):flip[index[b,a],j]=1
    total=np.zeros((n,n),dtype=object);E=np.eye(n,dtype=object)
    for r in range(k+1):
        if r:E=transfer(d,k+r-1,k-r+1)@E
        lower=metric(d,k+r,k-r)
        adj=np.array([[F(int(E[j,i])*int(lower[j]),int(g[i])) for j in range(E.shape[0])] for i in range(n)],dtype=object)
        total+=F((-1)**(k+r),math.factorial(r)**2)*(adj@E)
    assert np.array_equal(total,flip)
    print('planar ladder exchange',dict(d=d,k=k,dimension=n),'EXACT PASS',flush=True)

if __name__=='__main__':
    for d,p,q in [(2,2,2),(2,4,2),(2,3,3),(2,6,3),(2,4,4),(2,8,4),(3,2,2),(3,4,2)]:
        verify_clasps(d,p,q)
    for d,k in [(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)]:verify_exchange(d,k)

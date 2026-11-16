"""Exact audits for the diagrammatic two-block proof. Standard library only.

The proof for every k is the counting and bending argument in the note.
These checks independently audit TL signs, all small operator entries,
factorials, and the original complex Gram permanent normalization.
"""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
import itertools as it
import math
import random


def identity(n):return tuple(list(range(n,2*n))+list(range(n)))


def generator(n,i):
    p=list(identity(n));p[i]=i+1;p[i+1]=i;p[n+i]=n+i+1;p[n+i+1]=n+i
    return tuple(p)


@lru_cache(None)
def glue(a,b):
    """Stack a above b: multiplication means a after b."""
    n=len(a)//2;assert len(b)==2*n
    parent=list(range(4*n))
    def root(i):
        while parent[i]!=i:parent[i]=parent[parent[i]];i=parent[i]
        return i
    def join(i,j):parent[root(i)]=root(j)
    for i in range(2*n):join(i,a[i]);join(2*n+i,2*n+b[i])
    for i in range(n):join(i,3*n+i)
    ends=defaultdict(list)
    for i in range(4*n):ends[root(i)]
    for i in range(n):ends[root(2*n+i)].append(i);ends[root(n+i)].append(n+i)
    p=[None]*(2*n);loops=0
    for xs in ends.values():
        if not xs:loops+=1
        else:
            assert len(xs)==2
            x,y=xs;p[x]=y;p[y]=x
    return tuple(p),loops


def add(a,b,factor=Q(1)):
    out=a.copy()
    for p,c in b.items():
        out[p]=out.get(p,Q(0))+factor*c
        if not out[p]:del out[p]
    return out


def multiply(a,b):
    out={}
    for p,c in a.items():
        for q,d in b.items():
            r,loops=glue(p,q);out[r]=out.get(r,Q(0))+c*d*2**loops
    return {p:c for p,c in out.items() if c}


def tensor(a,b):
    out={}
    for p,c in a.items():
        for q,d in b.items():
            m=len(p)//2;n=len(q)//2;N=m+n;r=[0]*(2*N)
            def A(i):return i if i<m else N+i-m
            def B(i):return m+i if i<n else N+m+i-n
            for i in range(2*m):r[A(i)]=A(p[i])
            for i in range(2*n):r[B(i)]=B(q[i])
            out[tuple(r)]=c*d
    return out


def adjoint(a):
    out={}
    for p,c in a.items():
        n=len(p)//2;out[tuple((p[(i+n)%(2*n)]+n)%(2*n) for i in range(2*n))]=c
    return out


def trace(a):
    ans=Q(0)
    for p,c in a.items():
        n=len(p)//2;seen=set();loops=0
        for i in range(2*n):
            if i in seen:continue
            loops+=1;todo=[i];seen.add(i)
            while todo:
                x=todo.pop()
                for y in [p[x],(x+n)%(2*n)]:
                    if y not in seen:seen.add(y);todo.append(y)
        ans+=c*2**loops
    return ans


@lru_cache(None)
def jw(n):
    if n==1:return {identity(1):Q(1)}
    P=tensor(jw(n-1),{identity(1):Q(1)});e={generator(n,n-2):Q(1)}
    return add(P,multiply(multiply(P,e),P),-Q(n-1,n))


def exchange(k,r):
    p=list(range(2*k))
    for j in range(r):p[k-r+j],p[k+j]=p[k+j],p[k-r+j]
    return p


def reduced_word(p):
    current=list(range(len(p)));word=[]
    for i,target in enumerate(p):
        j=current.index(target)
        while j>i:
            current[j-1],current[j]=current[j],current[j-1];word.append(j-1);j-=1
    assert current==p
    return word


def audit_tl():
    for n in range(1,7):
        P=jw(n);assert adjoint(P)==P and multiply(P,P)==P and trace(P)==n+1
        for i in range(n-1):
            e={generator(n,i):Q(1)};assert not multiply(e,P) and not multiply(P,e)
            assert multiply(e,e)=={p:2*c for p,c in e.items()}
            for j in range(n-1):
                f={generator(n,j):Q(1)}
                if abs(i-j)==1:assert multiply(multiply(e,f),e)==e
                if abs(i-j)>1:assert multiply(e,f)==multiply(f,e)
        print('Jones--Wenzl',n,': idempotence, adjoint, turnbacks and trace EXACT PASS',flush=True)
    for k in range(1,4):
        n=2*k;K=tensor(jw(k),jw(k));I={identity(n):Q(1)};rhs={}
        for r in range(k+1):
            word=reduced_word(exchange(k,r));assert len(word)==r*r
            T=K
            for i in word:T=multiply(T,add(I,{generator(n,i):Q(1)},-1))
            T=multiply(T,K);rhs=add(rhs,T,math.comb(k,r)**2)
        assert not add(rhs,jw(n),-math.comb(n,k))
        print('Two-block TL identity k=',k,': every diagram coefficient EXACT PASS',flush=True)
    for k in range(1,5):
        counts=[0]*(k+1)
        for p in it.permutations(range(2*k)):counts[sum(p[i]>=k for i in range(k))]+=1
        assert counts==[math.factorial(k)**2*math.comb(k,r)**2 for r in range(k+1)]
    print('All double-coset multiplicities for k=1,2,3,4: EXACT PASS',flush=True)


def powers(d,k):
    if d==1:return [(k,)]
    return [(i,)+a for i in range(k+1) for a in powers(d-1,k-i)]


def factorial(a):return math.prod(math.factorial(x) for x in a)


def audit_fock(d,k):
    basis=list(it.product(powers(d,k),repeat=2));images=[{b:1} for b in basis];form=defaultdict(Q)
    for r in range(k+1):
        rows=defaultdict(list)
        for j,image in enumerate(images):
            for b,c in image.items():rows[b].append((j,c))
        for (a,b),entries in rows.items():
            weight=Q(factorial(a)*factorial(b),math.factorial(r)**2)
            for i,c in entries:
                for j,e in entries:form[i,j]+=weight*c*e
        if r==k:break
        lower=[]
        for image in images:
            out=defaultdict(int)
            for (a,b),c in image.items():
                for s in range(d):
                    if a[s] and b[s]:
                        aa=list(a);bb=list(b);aa[s]-=1;bb[s]-=1
                        out[tuple(aa),tuple(bb)]+=c*a[s]*b[s]
            lower.append(dict(out))
        images=lower
    for i,(a,b) in enumerate(basis):
        for j,(c,e) in enumerate(basis):
            left=tuple(x+y for x,y in zip(a,e));right=tuple(x+y for x,y in zip(c,b))
            expected=factorial(left) if left==right else 0
            assert form[i,j]==expected
    print('Fock identity d=',d,'k=',k,'dimension=',len(basis),': every form entry EXACT PASS',flush=True)


def occupation(word,d):return tuple(word.count(i) for i in range(d))


def audit_bending(d,k):
    alphas=powers(d,k)
    words={a:sorted(set(it.permutations(tuple(i for i,n in enumerate(a) for _ in range(n))))) for a in alphas}
    sizes={a:len(w) for a,w in words.items()};basis=list(it.product(alphas,repeat=2))
    for r in range(k+1):
        p=exchange(k,r);images=[]
        for a,b in basis:
            image=defaultdict(Q)
            for u in words[a]:
                for v in words[b]:
                    if not r or u[k-r:]==v[k-r:]:image[u[:k-r]+v[:k-r]]+=Q(1,sizes[a]*sizes[b])
            images.append(image)
        for i,(a,b) in enumerate(basis):
            for j,(c,e) in enumerate(basis):
                gram=sum(x*images[j].get(w,0) for w,x in images[i].items())
                count=0
                for u in words[c]:
                    for v in words[b]:
                        out=[None]*(2*k)
                        for s,x in enumerate(u+v):out[p[s]]=x
                        if occupation(out[:k],d)==a and occupation(out[k:],d)==e:count+=1
                target=Q(count,sizes[a]*sizes[b]*sizes[c]*sizes[e])
                assert gram==target,(d,k,r,i,j,gram,target)
        print('Physical bending d=',d,'k=',k,'r=',r,': every tensor entry EXACT PASS',flush=True)


def gauss_add(a,b):return a[0]+b[0],a[1]+b[1]
def gauss_mul(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def gauss_conj(a):return a[0],-a[1]
def gauss_sum(xs):
    out=(0,0)
    for x in xs:out=gauss_add(out,x)
    return out
def gauss_product(xs):
    out=(1,0)
    for x in xs:out=gauss_mul(out,x)
    return out
def permanent(A):return gauss_sum(gauss_product(A[i][p[i]] for i in range(len(A))) for p in it.permutations(range(len(A))))


def audit_original():
    rng=random.Random(20261101)
    for k in [1,2,3]:
        for case in range(3):
            d=4;vs=[[(rng.randrange(-2,3),rng.randrange(-2,3)) for _ in range(d)] for _ in range(2*k)]
            A=[[gauss_sum(gauss_mul(gauss_conj(x),y) for x,y in zip(u,v)) for v in vs] for u in vs]
            G=[[permanent([row[j*k:(j+1)*k] for row in A[i*k:(i+1)*k]]) for j in range(2)] for i in range(2)]
            def poly(vectors):
                P={(0,)*d:(1,0)}
                for v in vectors:
                    out=defaultdict(lambda:(0,0))
                    for a,c in P.items():
                        for i,x in enumerate(v):
                            b=list(a);b[i]+=1;b=tuple(b);out[b]=gauss_add(out[b],gauss_mul(c,x))
                    P=out
                return P
            P=poly(vs)
            norm=sum(factorial(a)*(c[0]**2+c[1]**2) for a,c in P.items())
            lhs=permanent(A);rhs=permanent(G)
            assert lhs==(norm,0) and rhs[1]==0 and lhs[0]>=rhs[0]
            coefficients=[(0,0)]*(k+1)
            for perm in it.permutations(range(2*k)):
                r=sum(perm[i]>=k for i in range(k))
                coefficients[r]=gauss_add(coefficients[r],gauss_product(A[i][perm[i]] for i in range(2*k)))
            f=poly(vs[:k]);h=poly(vs[k:])
            image={(a,b):gauss_mul(c,gauss_conj(e)) for a,c in f.items() for b,e in h.items()}
            for r in range(k+1):
                square=sum(factorial(a)*factorial(b)*(c[0]**2+c[1]**2) for (a,b),c in image.items())
                value=Q(square,math.factorial(r)**2)
                assert value.denominator==1 and coefficients[r]==(value.numerator,0)
                if r==k:break
                lower=defaultdict(lambda:(0,0))
                for (a,b),c in image.items():
                    for s in range(d):
                        if a[s] and b[s]:
                            aa=list(a);bb=list(b);aa[s]-=1;bb[s]-=1
                            z=gauss_mul((a[s]*b[s],0),c);key=(tuple(aa),tuple(bb))
                            lower[key]=gauss_add(lower[key],z)
                image=lower
    assert permanent([[(1,0)]*4 for _ in range(4)])==(24,0)
    assert permanent([[(2,0)]*2 for _ in range(2)])==(8,0)
    print('Nine complex Gram/Fock normalizations, every Lieb polynomial coefficient, and 24-8=16: EXACT PASS',flush=True)


def audit_unbent():
    w={(0,0,1,1):Q(1),(1,1,0,0):Q(1)}
    for a in [(0,1),(1,0)]:
        for b in [(0,1),(1,0)]:w[a+b]=-Q(1,2)
    E=defaultdict(Q)
    for perm in it.permutations(range(4)):
        for word,c in w.items():
            out=tuple(word[perm[i]] for i in range(4));E[out]+=c/Q(24)
    assert not any(E.values())
    assert {word[2:]+word[:2]:c for word,c in w.items()}==w
    assert sum(c*c for c in w.values())==3
    print('Explicit negative unbent eigenvector: E w=0, S w=w, X w=-2 w: EXACT PASS',flush=True)


if __name__=='__main__':
    audit_tl()
    for d,k in [(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4),(4,2)]:audit_fock(d,k)
    for d,k in [(3,2),(4,2),(2,3)]:audit_bending(d,k)
    audit_original();audit_unbent()
    print('ALL TWO-BLOCK TL AUDITS PASSED',flush=True)

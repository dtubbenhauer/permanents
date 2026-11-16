import itertools as it, math
import numpy as np

def comps(n,d):
    if d==1: return [(n,)]
    return [(i,)+a for i in range(n+1) for a in comps(n-i,d-1)]
def mf(a): return math.prod(math.factorial(x) for x in a)
def pmatrix(n,p):
    a=np.zeros((n**3,n**3))
    for v in it.product(range(n),repeat=3):
        w=tuple(v[i] for i in p)
        a[np.ravel_multi_index(w,(n,)*3),np.ravel_multi_index(v,(n,)*3)]=1
    return a
def pt(a,n):
    return a.reshape((n,)*6).transpose(0,1,5,3,4,2).reshape((n**3,n**3))
def run(d,k):
    bs=comps(k,d); bs2=comps(2*k,d); bs3=comps(3*k,d)
    n=len(bs); N=n**3; lookup2={a:i for i,a in enumerate(bs2)}; lookup3={a:i for i,a in enumerate(bs3)}
    mu=np.zeros((len(bs2),n*n)); mus=np.zeros((len(bs3),N))
    for i,a in enumerate(bs):
        for j,b in enumerate(bs):
            ab=tuple(x+y for x,y in zip(a,b))
            mu[lookup2[ab],i*n+j]=math.sqrt(mf(ab)/mf(a)/mf(b))
            for l,c in enumerate(bs):
                abc=tuple(x+y for x,y in zip(ab,c))
                mus[lookup3[abc],(i*n+j)*n+l]=math.sqrt(mf(abc)/mf(a)/mf(b)/mf(c))
    aa=math.comb(2*k,k); cc=math.factorial(3*k)//math.factorial(k)**3
    Pi=np.kron(mu.T@mu/aa,np.eye(n)); Pi23=np.kron(np.eye(n),mu.T@mu/aa)
    E=mus.T@mus/cc; R=sum(pmatrix(n,p) for p in it.permutations(range(3)))/6
    ff=(np.eye(N)+pmatrix(n,(1,0,2)))/2
    L=np.zeros((N,n))
    for i,j in it.product(range(n),repeat=2): L[(i*n+j)*n+j,i]=1
    U=L.T@ff; V=L.T@Pi
    X=cc*E-6*R
    Q=X+9*aa/4*(2*R@Pi@R-Pi@R-R@Pi)
    P=pt(Q,n)
    rhs=2*ff@(aa*pt(Pi23,n)-np.eye(N))@ff+(cc*pt(E,n)-aa*Pi)-4*U.T@U-aa/2*(U.T@V+V.T@U)
    avg=sum(S.T@Q@S for S in [pmatrix(n,p) for p in it.permutations(range(3))])/6
    print({'d':d,'k':k,'N':N,'bent_identity_residual':float(np.max(np.abs(P-rhs))),'avg_residual':float(np.max(np.abs(avg-X))),'min_bent_eigenvalue':float(np.linalg.eigvalsh(P)[0])},flush=True)
if __name__=='__main__':
    for d,k in [(2,2),(2,3),(3,2),(2,4),(3,3)]: run(d,k)

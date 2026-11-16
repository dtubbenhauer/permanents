"""Exact audits for Block_permanents_clasps_webs.tex.

Run from this directory with Python 3 and numpy. All matrix entries in
the tests are integers or fractions.Fraction; no numerical eigensolver.
"""
from fractions import Fraction as F
from itertools import product, permutations
from math import comb, factorial, prod
from pathlib import Path
import runpy
import numpy as np
from audit_web_clasps import verify_clasps, harmonic, basis


def eps(*a):
    if len(set(a)) != len(a):
        return 0
    return (-1) ** sum(x > y for i, x in enumerate(a) for y in a[i+1:])


def permutation_matrix(d, p):
    words = list(product(range(d), repeat=len(p)))
    index = {x: i for i, x in enumerate(words)}
    out = np.zeros((len(words), len(words)), dtype=object)
    for j, w in enumerate(words):
        out[index[tuple(w[p[i]] for i in range(len(p)))], j] = 1
    return out


def a2_relations():
    for a, b in product(range(3), repeat=2):
        assert sum(eps(a,i,j)*eps(b,i,j) for i,j in product(range(3),repeat=2)) == 2*(a==b)
    for a,b,c,d in product(range(3),repeat=4):
        lhs=sum(eps(a,x,y)*eps(b,x,z)*eps(c,y,w)*eps(d,z,w)
                for x,y,z,w in product(range(3),repeat=4))
        assert lhs == (a==b)*(c==d)+(a==c)*(b==d)
    for d in (2,3):
        I=np.eye(d**3,dtype=object)
        s1=permutation_matrix(d,(1,0,2))
        s2=permutation_matrix(d,(0,2,1))
        h1,h2=I-s1,I-s2
        alt=sum(eps(*p)*permutation_matrix(d,p) for p in permutations(range(3)))
        assert np.array_equal(h1@h1,2*h1)
        assert np.array_equal(h1@h2@h1-h1,alt)
        assert np.array_equal(alt@alt,6*alt)
        assert np.trace(alt)==(6 if d==3 else 0)
        sym=F(1,6)*sum(permutation_matrix(d,p) for p in permutations(range(3)))
        assert np.array_equal(sym@sym,sym)
        assert np.trace(sym)==comb(d+2,3)
        assert not np.any(sym@h1)
        if d==3:
            epsilon=np.array([eps(*w) for w in product(range(3),repeat=3)],dtype=object)
            assert np.array_equal(alt,np.outer(epsilon,epsilon))
    print('A2 epsilon digon, square, determinant channel, and c30: EXACT PASS')


def recoupling():
    # Orthogonal unnormalized vectors; their norms are 6,2,6,2.
    L=[(2,-1,-1),(0,1,-1)]
    R=[(1,1,-2),(1,-1,0)]
    dots=[[sum(a*b for a,b in zip(x,y)) for y in R] for x in L]
    assert dots==[[3,3],[3,-1]]
    norms=[6,2]
    overlaps=[[F(dots[i][j]**2,norms[i]*norms[j]) for j in range(2)] for i in range(2)]
    assert overlaps==[[F(1,4),F(3,4)],[F(3,4),F(1,4)]]
    for d,target in ((2,2),(3,8)):
        I=np.eye(d**3,dtype=object)
        S=F(1,6)*sum(permutation_matrix(d,p) for p in permutations(range(3)))
        A=F(1,6)*sum(eps(*p)*permutation_matrix(d,p) for p in permutations(range(3)))
        mixed=I-S-A
        left=mixed@(F(1,2)*(I+permutation_matrix(d,(1,0,2))))
        right=mixed@(F(1,2)*(I+permutation_matrix(d,(0,2,1))))
        assert np.trace(left)==target
        assert np.trace(left@right)==F(target,4)
    print('TL and A2 fundamental recoupling, including phases: EXACT PASS')


def trace_maps():
    for d in (2,3,4):
        for i in range(d):
            for j in range(i,d):
                z=np.zeros((d,d),dtype=object)
                z[i,j]=z[j,i]=1
                LA=np.zeros((d,)*4,dtype=object)
                LB=np.zeros((d,)*4,dtype=object)
                for a,b,c,t in product(range(d),repeat=4):
                    LA[a,b,c,t]=F((a==t)*z[b,c]+(b==t)*z[a,c]+(c==t)*z[a,b],3)
                    LB[a,b,c,t]=F(-(a==t)*z[b,c],3)+F((b==t)*z[a,c]+(c==t)*z[a,b],6)
                ta=np.zeros((d,d),dtype=object)
                tb=np.zeros((d,d),dtype=object)
                for a,b in product(range(d),repeat=2):
                    ta[a,b]=sum(LA[t,a,b,t] for t in range(d))
                    tb[a,b]=sum(LB[a,t,b,t] for t in range(d))
                assert np.array_equal(ta,F(d+2,3)*z)
                assert np.array_equal(tb,F(d-1,6)*z)
                assert sum(x*x for x in LA.flat)==F(d+2,3)*sum(x*x for x in z.flat)
                assert sum(x*x for x in LB.flat)==F(d-1,6)*sum(x*x for x in z.flat)
                assert sum(x*y for x,y in zip(LA.flat,LB.flat))==0
    for d in (3,4):
        aa=F(7*(d+8),d+2);bb=F(2*(7-d),d-1)
        shift=F(5,2)/bb
        rem=aa-bb*shift**2
        expected={3:(F(5,8),F(1107,80)),4:(F(5,4),F(87,8))}[d]
        assert (shift,rem)==expected
        assert rem>0 and bb>0
    print('Quadratic trace maps and four-square coefficients at d=3,4: EXACT PASS')


def coefficient_checks():
    k,d=3,6
    a=comb(2*k,k);n=comb(d+k-1,k);lam=comb(d+2*k-1,k);Lam=comb(d+3*k-1,k)
    alpha=F(2*(lam-1),n)-4;eta=F(a*a*(Lam-1),lam)
    assert alpha==F(13,7)
    assert F(a,2)/alpha==F(70,13)
    assert eta-F(a*a,4)/alpha==F(10740,13)
    def nr(p,q,r):return factorial(r)*prod(range(d+p+q-2*r,d+p+q-r))
    Ac=[F(2*(comb(d+2*k-1,r)-1),nr(k,k,r)) for r in range(1,k)]
    Bc=[F(comb(d+3*k-1,r)-1,nr(2*k,k,r)) for r in range(1,k)]
    assert Ac==[2,F(3,4)] and Bc==[1,F(15,44)]
    print('Six cubic-square coefficients, with d=6: EXACT PASS')


def quadratic_average(env):
    for D, (_, count) in env['web_reps'].items():
        values=[]
        for r in range(3):
            order=[(r+i)%3 for i in range(3)]
            rotated=tuple(D[3*order[i]+order[j]] for i in range(3) for j in range(3))
            values.append(env['web_coeff'](rotated,count))
        target=F(8,prod(factorial(x) for x in D))-(all(x in (0,2) for x in D))
        assert sum(values)==3*target
    # A separate polynomial check: raw polynomial of F is sum F_ij z_i z_j.
    # Its unitary Fock polynomial is that polynomial divided by sqrt(2).
    from collections import defaultdict
    import random
    rng=random.Random(20261101)
    def poly(Fmat,d):
        out=defaultdict(int)
        for (a,b),v in Fmat.items():
            e=[0]*d;e[a]+=1;e[b]+=1;out[tuple(e)]+=v
        return dict(out)
    def mul(f,g):
        out=defaultdict(int)
        for a,x in f.items():
            for b,y in g.items():out[tuple(u+v for u,v in zip(a,b))]+=x*y
        return dict(out)
    for d in (3,4):
        for trial in range(3):
            packets=[]
            for s in range(3):
                f={}
                for a in range(d):
                    for b in range(a,d):
                        v=rng.randrange(-2,3);f[a,b]=v;f[b,a]=v
                packets.append(f)
            g=[[env['web_dot'](a,b) for b in packets] for a in packets]
            pg=sum(prod(g[i][p[i]] for i in range(3)) for p in permutations(range(3)))
            polys=[poly(f,d) for f in packets]
            total=mul(mul(polys[0],polys[1]),polys[2])
            norm=sum(x*x*prod(factorial(v) for v in e) for e,x in total.items())
            delta=F(norm,8)-pg
            ptotal=sum(env['web_bilinear'](packets[r:]+packets[:r],packets[r:]+packets[:r]) for r in range(3))
            assert 3*delta==ptotal
    print('Quadratic cyclic average and six independent Fock normalization audits: EXACT PASS')


if __name__=='__main__':
    root=Path(__file__).resolve().parent
    a2_relations();recoupling()
    for d,p,q in [(2,2,2),(2,6,3),(3,1,1),(3,2,2),(3,4,2)]:
        verify_clasps(d,p,q)
    assert np.trace(harmonic(3,1,1))==8
    assert np.trace(harmonic(3,2,2))==27
    assert np.trace(harmonic(3,3,1))==24
    assert np.trace(harmonic(3,1,2))==15
    env=runpy.run_path(str(root/'verify_quadratic_transport.py'),run_name='__main__')
    quadratic_average(env)
    trace_maps();coefficient_checks()
    runpy.run_path(str(root/'verify_tl_two_blocks.py'),run_name='__main__')
    print('ALL SL2 / SL3 DIAGRAM AUDITS PASSED')

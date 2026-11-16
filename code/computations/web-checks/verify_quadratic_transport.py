# Formal, exact verification of the short contraction identity.
# Each dict is a tensor in the ordinary, unnormalized real strand basis.
import itertools as it
import math
from collections import defaultdict
from fractions import Fraction as Rat

def web_pair(a,b):
    out={(a,b):1}
    if a!=b:out[b,a]=1
    return out

def web_C(F,H,J):
    out=defaultdict(Rat)
    for L,M in ((F,H),(H,F)):
        for (a,s),x in L.items():
            for (ss,d),z in J.items():
                if s!=ss:continue
                for (b,c),y in M.items():out[a,b,c,d]+=x*y*z
    return dict(out)

def web_sym(C):
    out=defaultdict(Rat)
    for inds,v in C.items():
        for p in it.permutations(range(3)):
            out[tuple(inds[q] for q in p)+(inds[3],)]+=Rat(v,6)
    return dict(out)

def web_trace(C,slot):
    out=defaultdict(Rat)
    for inds,v in C.items():
        if inds[slot]==inds[3]:
            out[tuple(inds[q] for q in range(3) if q!=slot)]+=v
    return dict(out)

def web_dot(C,D):return sum(v*D.get(key,0) for key,v in C.items())

def web_bilinear(left,right):
    C,D=web_C(*left),web_C(*right)
    t,u=web_trace(C,0),web_trace(C,1)
    tt,uu=web_trace(D,0),web_trace(D,1)
    return (2*web_dot(C,D)+12*web_dot(web_sym(C),web_sym(D))
        +Rat(3,2)*(web_dot(t,uu)+web_dot(u,tt))+4*web_dot(u,uu))

# Reconstruct representatives here, so this cell is independent of source files.
web_reps={}
for perm in it.permutations(range(6)):
    D=[0]*9
    for i,j in enumerate(perm):D[(i//2)*3+j//2]+=1
    D=tuple(D)
    if D not in web_reps:web_reps[D]=[perm,0]
    web_reps[D][1]+=1

def web_coeff(D,n):
    if n==8:return 0
    if n==64:return 8
    assert n==32
    trace=D[0]+D[4]+D[8]
    if trace==4:return 12-6*D[8]
    assert trace==1
    return 3+3*D[8]

col=(web_pair(0,1),web_pair(2,3),web_pair(4,5))
for D,(perm,count) in web_reps.items():
    row=tuple(web_pair(*perm[j:j+2]) for j in range(0,6,2))
    # Partial transposition exchanges the third input and output packets.
    value=web_bilinear((row[0],row[1],col[2]),
                       (col[0],col[1],row[2]))
    # Distinct strand labels isolate exactly one transport pattern.
    expected=web_coeff(D,count)*math.prod(math.factorial(x) for x in D)
    assert value==expected,(D,value,expected)
print('All 21 formal contraction / transport coefficients: EXACT PASS')

# Exact scalar matrix and square completion in dimension four.
aa,bb,cross=Rat(14),Rat(2),Rat(5)
assert aa*bb-(cross/2)**2==Rat(87,4)>0
assert aa-bb*Rat(5,4)**2==Rat(87,8)
assert 2*bb*Rat(5,4)==cross
print('Dimension-four trace matrix and square completion: EXACT PASS')

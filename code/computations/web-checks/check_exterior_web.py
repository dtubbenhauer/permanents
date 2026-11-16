from itertools import permutations
from fractions import Fraction as F
from collections import defaultdict
S=list(permutations(range(4)));i=tuple(range(4))
def perm(*cycles):
 x=list(i)
 for cycle in cycles:
  for a,b in zip(cycle,cycle[1:]+cycle[:1]):x[a]=b
 return tuple(x)
def add(*ds):
 z=defaultdict(F)
 for d in ds:
  for p,c in d.items():z[p]+=c
 return {p:c for p,c in z.items() if c}
def scale(d,c):return {p:v*c for p,v in d.items() if v*c}
def mul(a,b):
 z=defaultdict(F)
 for p,c in a.items():
  for q,d in b.items():z[tuple(p[q[j]] for j in range(4))]+=c*d
 return {p:c for p,c in z.items() if c}
def mult(*xs):
 a={i:F(1)}
 for b in xs:a=mul(a,b)
 return a
I={i:F(1)}
s12={perm((0,1)):F(1)};s34={perm((2,3)):F(1)}
s13={perm((0,2)):F(1)};s24={perm((1,3)):F(1)}
t={perm((0,2),(1,3)):F(1)}
P=scale(mul(add(I,s12),add(I,s34)),F(1,4))
f=scale(add(I,t),F(1,2))
A=scale(mul(add(I,scale(s13,-1)),add(I,scale(s24,-1))),F(1,4))
Pi={p:F(1,24) for p in S}
LHS=mult(P,f,A,f,P)
RHS=scale(add(mul(P,f),scale(Pi,-1)),F(3,4))
assert LHS==RHS,(LHS,RHS)
print('Exact S4 group-algebra identity: P f A13 A24 f P = (3/4)(P f - P4)')
# Output bubble after embedding wedge-square factors isometrically.
Q=scale(mul(add(I,scale(s12,-1)),add(I,scale(s34,-1))),F(1,4))
Pcross=scale(mul(add(I,s13),add(I,s24)),F(1,4))
def sign(p):return (-1)**sum(p[a]>p[b] for a in range(4) for b in range(a+1,4))
Alt={p:F(sign(p),24) for p in S}
assert scale(mult(Q,Pcross,Q),4)==scale(add(mul(Q,f),scale(Alt,-1)),3)
print('Exact output bubble: YY† = 3 sym(wedge2) - 3 antisym4')
assert mul(A,P)==mult(A,P,f)
print('Exact packet symmetry: Yt = Y')

from itertools import permutations,product
from fractions import Fraction
import random

def dot(x,y):return sum(a*b for a,b in zip(x,y))
def permanent(A):return sum(prod(A[i][p[i]] for i in range(len(A))) for p in permutations(range(len(A))))
def prod(x):
 z=1
 for a in x:z*=a
 return z

def gram(vs):return [[dot(x,y) for y in vs] for x in vs]
def pairgram(packets):
 return [[dot(x,u)*dot(y,v)+dot(x,v)*dot(y,u) for u,v in packets] for x,y in packets]
def delta(packets):
 return permanent(gram([v for pair in packets for v in pair]))-permanent(pairgram(packets))
random.seed(229)
for trial in range(12):
 x,y=[[random.randint(-2,2) for _ in range(6)] for _ in range(2)]
 gs=[[random.randint(-2,2) for _ in range(4)]+[0,0] for _ in range(4)]
 x0=x[:4]+[0,0]; y0=y[:4]+[0,0]
 x1=[0]*4+x[4:];y1=[0]*4+y[4:]
 packets=[(x,y),(gs[0],gs[1]),(gs[2],gs[3])]
 projected=[(x0,y0)]+packets[1:]
 lhs=delta(packets)-delta(projected)
 d2=delta(packets[1:])
 ps=[[x0[a]*y1[j]+y0[a]*x1[j] for a in range(4)] for j in (4,5)]
 norm1=sum(dot(p,p) for p in ps)
 norm2=dot(x1,x1)*dot(y1,y1)+dot(x1,y1)**2
 contractions=0
 for p in ps:
  # T=P4(G tensor H)=1/12 sum of ordered elementary four-tensors.
  capnums=[]
  for abc in product(range(4),repeat=3):
   capnums.append(sum(dot(p,gs[perm[0]][:4])*prod(gs[perm[r+1]][abc[r]] for r in range(3)) for perm in permutations(range(4))))
  contractions+=Fraction(sum(z*z for z in capnums),144)
 rhs=(norm1+norm2)*d2+24*contractions
 assert lhs==rhs,(trial,lhs,rhs)
 print('PASS exact rank reduction',trial+1)

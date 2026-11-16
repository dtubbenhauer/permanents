from itertools import combinations_with_replacement, permutations
from math import factorial, comb
from fractions import Fraction as F
from collections import Counter

def orbit(t):
 z=factorial(len(t))
 for m in Counter(t).values():z//=factorial(m)
 return z

def dot(x,y):return sum(a*b for a,b in zip(x,y))
for d in (2,3,4):
 basis=list(combinations_with_replacement(range(d),2));n=len(basis)
 words=[set(permutations(x)) for x in basis];met=[len(x) for x in words]
 pairs=[(i,j) for i in range(n) for j in range(n)]
 g=[F(met[i],met[j]) for i,j in pairs]
 c=[]
 for a in range(d):
  for b in range(d):
   c.append([F(sum(x[0]==a and y[0]==b and x[1]==y[1] for x in words[i] for y in words[j]),met[j]) for i,j in pairs])
 B=[[sum(c[a][s]*c[b][s]/g[s] for s in range(n*n)) for b in range(d*d)] for a in range(d*d)]
 expect=[[F(d+2,4)*(a==b)+F(1,4)*(a//d==a%d and b//d==b%d) for b in range(d*d)] for a in range(d*d)]
 assert B==expect,(d,'bubble')
 bval=sum(B[a][a] for a in range(d*d))
 hval=sum(B[a][b]*B[b][a] for a in range(d*d) for b in range(d*d))
 co=[sum(row[s] for s,(i,j) in enumerate(pairs) if i==j) for row in c]
 mixed=sum(x*x for x in co)
 assert bval==mixed==F(d*(d+1)**2,4)
 assert hval==F(d*(d+1)*(d*d+3*d+4),16)
 P=[]
 for a,b in pairs:
  rr=[]
  out=sorted(basis[a]+basis[b])
  for i,j in pairs:
   inp=sorted(basis[i]+basis[j])
   rr.append(F(met[i]*met[j],orbit(inp)) if out==inp else F(0))
  P.append(rr)
 J=[[3*(F((a==i and b==j)+(a==j and b==i),2)-P[r][s]) for s,(i,j) in enumerate(pairs)] for r,(a,b) in enumerate(pairs)]
 Z=[[J[a*n+j][i*n+b] for i,j in pairs] for a,b in pairs]
 W1=[[sum(c[t][r]*c[t][s] for t in range(d*d))/g[r] for s in range(n*n)] for r in range(n*n)]
 W2=[[F(a==b and i==j) for i,j in pairs] for a,b in pairs]
 S=[[F(r==s)-2*W1[r][s]+W2[r][s] for s in range(n*n)] for r in range(n*n)]
 assert Z==S,(d,'bend')
 z0=sum(Z[r][r] for r in range(n*n))
 z2=sum(Z[r][s]*W2[r][s]*g[r]/g[s] for r in range(n*n) for s in range(n*n))
 z1=sum(Z[r][s]*W1[r][s]*g[r]/g[s] for r in range(n*n) for s in range(n*n))
 znorm=sum(Z[r][s]**2*g[r]/g[s] for r in range(n*n) for s in range(n*n))
 q=F(d*d*(d*d-1),12)
 assert (z0,z1,z2,znorm)==(3*q,-F(3,2)*q,3*q,9*q)
 G=[[n*n,bval,n],[bval,hval,bval],[n,bval,n*n]]
 print('PASS d=',d,' G=',G,' Z pairings=',(z0,z1,z2),' squared norm=',znorm,flush=True)

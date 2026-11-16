import json,numpy as np,scipy.linalg as la,sympy as S
from pathlib import Path
from fractions import Fraction
p=Path('two_bends');j=json.loads((p/'rational38_d6.json').read_text());q=[S.Rational(s)for s in j['coefficients']];x=np.array([float(z)for z in q]);A=S.Matrix(j['scalar_constraint_matrix']);b=S.Matrix(j['scalar_rhs']);assert A*S.Matrix(q)==b;print('exact scalar equations',A.rows,'rank',A.rank(),'passed')
mins=[];zeros=[]
for kind,fn in [('one','one_d6.npz'),('two','blocks38_d6.npz')]:
 z=np.load(p/fn);stride=2 if kind=='one'else 4
 for i in range(len(z.files)//stride):
  H=z[f'h{i}'];base=np.zeros_like(H[0])if kind=='one'else H[0];co=H if kind=='one'else H[1:];coeff=x[24:]if kind=='one'else x;M=base+np.einsum('k,kij->ij',coeff,co);ev=la.eigvalsh(M);w=z[f'w{i}'].tolist();sector=[]if kind=='one'else [int(z[f's{i}']),int(z[f't{i}'])]
  if ev[0]<1e-7:
   assert M.shape==(1,1)
   rat=[S.Rational(str(v)).limit_denominator(1000000)for v in co[:,0,0]];const=S.Rational(str(base[0,0])).limit_denominator(1000000);r=const+sum(a*b for a,b in zip(q[24:]if kind=='one'else q,rat));assert r==0
   assert max(abs(float(a)-v)for a,v in zip(rat,co[:,0,0]))<1e-11
   zeros.append([kind,sector,w,float(ev[0])])
  else:mins.append([float(ev[0]),kind,sector,w])
print('all nearzero blocks scalar and exact rational zero',len(zeros));print('zero blocks',zeros);print('minimum positive',min(mins))

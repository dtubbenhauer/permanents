import json,numpy as np,scipy.linalg as la,sympy as S
from pathlib import Path
p=Path('two_bends');j=json.loads((p/'one_exact_d6.json').read_text());coef=json.loads(Path('two_bends/rational38_d6.json').read_text())['coefficients'];assert j['coefficients']==coef[24:]
z=np.load('two_bends/one_d6.npz');x=np.array([float(S.Rational(v))for v in coef[24:]]);mat=lambda t:S.Matrix([[S.Rational(v)for v in r]for r in t]);worst=0;dim=rank=0
for b in j['blocks']:
 H=mat(b['H']);G=mat(b['G']);mult=H.rows
 assert G.det()>0
 if H==S.zeros(mult):assert mult==1;r=0
 else:
  minors=[H[:i,:i].det()for i in range(1,mult+1)];assert all(a>0 for a in minors);r=mult
 dim+=int(b['irrep_dimension'])*mult;rank+=int(b['irrep_dimension'])*r
 i=next(i for i in range(len(z.files)//2)if list(z[f'w{i}'])==b['weight']);N=np.einsum('k,kij->ij',x,z[f'h{i}']);ev=la.eigvalsh(np.array(H,float),np.array(G,float));en=la.eigvalsh(N);err=max(abs(ev-en));worst=max(worst,float(err));print(b['weight'],'H/G eigens',ev,'cached',en,'error',err)
print('TOTAL',dim,'rank',rank,'maxspectralerror',worst);assert dim==37191 and worst<1e-8

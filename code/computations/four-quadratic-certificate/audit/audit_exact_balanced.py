import json,numpy as np,scipy.linalg as la,sympy as S
from pathlib import Path
p=Path('two_bends');coef=json.loads(Path('two_bends/rational38_d6.json').read_text())['coefficients'];x=np.array([float(S.Rational(v))for v in coef]);z=np.load('two_bends/blocks38_d6.npz');mat=lambda t:S.Matrix([[S.Rational(v)for v in r]for r in t]);worst=0;dims={};ranks={}
for sec in [(1,1),(1,-1),(-1,-1)]:
 j=json.loads((p/f'balanced_{sec[0]}_{sec[1]}.json').read_text());assert j['coefficients']==coef;dim=rank=0
 for b in j['blocks']:
  H=mat(b['H']);G=mat(b['G']);m=H.rows
  assert all(G[:i,:i].det()>0 for i in range(1,m+1))
  if H==S.zeros(m):assert m==1;r=0
  else:assert all(H[:i,:i].det()>0 for i in range(1,m+1));r=m
  dim+=b['dimension']*m;rank+=b['dimension']*r
  i=next(i for i in range(len(z.files)//4)if int(z[f's{i}'])==sec[0]and int(z[f't{i}'])==sec[1]and list(z[f'w{i}'])==b['weight']);A=z[f'h{i}'];N=A[0]+np.einsum('k,kij->ij',x,A[1:]);ev=la.eigvalsh(np.array(H,float),np.array(G,float));en=la.eigvalsh(N);err=max(abs(ev-en));worst=max(worst,float(err));print(sec,b['weight'],'error',err,'mineig',ev[0])
 dims[sec]=dim;ranks[sec]=rank;assert dim==j['dimension_so_far']and rank==j['rank_so_far']
print('dims',dims,'ranks',ranks,'full_dimension',dims[1,1]+2*dims[1,-1]+dims[-1,-1],'fullrank',ranks[1,1]+2*ranks[1,-1]+ranks[-1,-1],'maxspectralerror',worst)
assert dims[1,1]+2*dims[1,-1]+dims[-1,-1]==194481 and ranks[1,1]+2*ranks[1,-1]+ranks[-1,-1]==58031 and worst<1e-8

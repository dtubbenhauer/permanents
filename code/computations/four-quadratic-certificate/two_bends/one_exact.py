"""Exact one-bend half of the mixed certificate. No numerical projectors.

Raw monomials have factorial Fock norms. Triple packet tensors are
averages over all six orders. Coordinate permutations reduce pure weights
to partitions. Casimir spectral functions are rational interpolation
polynomials, evaluated with python-flint rational matrices.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
os.environ.setdefault('OMP_NUM_THREADS','1')
import itertools as it, math, json, sys, time
from pathlib import Path
from collections import defaultdict, Counter
import numpy as np
import scipy.sparse as sp
import sympy as S
from flint import fmpq_mat, fmpq

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent))
from check import comps,mf
from exact_twobend import exact_psd
LAM=[(8,),(7,1),(6,2),(5,3),(5,2,1),(4,4),(4,3,1),(4,2,2),(3,2,2,1),(2,2,2,2)]
OFF=[sum(x*(x+1-2*(i+1))for i,x in enumerate(lam))for lam in LAM]

def eye(n):
    a=fmpq_mat(n,n)
    for i in range(n):a[i,i]=1
    return a

def fm(a):
    return fmpq_mat([[fmpq(str(x))for x in row]for row in a])

def poly(coeff,C,I):
    ans=fmpq_mat(C.nrows(),C.ncols())
    for c in coeff:ans=ans*C+fmpq(str(c))*I
    return ans

def primitive_basis(K):
    out=[]
    for v in K.nullspace():
        v*=math.lcm(*[int(x.q)for x in v])
        v/=math.gcd(*[int(x)for x in v])
        out.append(v)
    return S.Matrix.hstack(*out)if out else S.zeros(K.cols,0)

def build(d,coefpath):
    started=time.time()
    cjson=json.loads(Path(coefpath).read_text())
    coeff=[S.Rational(x)for x in cjson['coefficients'][24:]]
    assert len(coeff)==14
    x=S.Symbol('x')
    fp=S.Poly(S.interpolate(list(zip(OFF,coeff[:10])),x),x).all_coeffs()
    rp=S.Poly(S.interpolate([(56,0),(28,coeff[10]),(16,0),(4,coeff[11]),(-16,0)],x),x).all_coeffs()
    bs=comps(2,d);n=len(bs);bl={a:i for i,a in enumerate(bs)}
    triples=list(it.combinations_with_replacement(range(n),3));tl={t:i for i,t in enumerate(triples)};N=len(triples)
    sums=[tuple(sum(bs[a][i]for a in t)for i in range(d))for t in triples]
    orb=[6//math.prod(math.factorial(v)for v in Counter(t).values())for t in triples]
    weights=[mf(a)for a in bs]
    gt=[S.Rational(math.prod(weights[a]for a in t),orb[j])for j,t in enumerate(triples)]
    E={};e={}
    for a,b in it.product(range(d),repeat=2):
        rr=[];cc=[];vv=[]
        for col,src in enumerate(triples):
            out=defaultdict(int)
            for r in range(3):
                al=bs[src[r]]
                if not al[b]:continue
                be=list(al);be[a]+=1;be[b]-=1;dest=list(src);dest[r]=bl[tuple(be)]
                out[tl[tuple(sorted(dest))]]+=al[b]
            for row,v in out.items():rr.append(row);cc.append(col);vv.append(v)
        E[a,b]=sp.csr_matrix((vv,(rr,cc)),shape=(N,N),dtype=np.int64)
        rr=[];cc=[];vv=[]
        for col,al in enumerate(bs):
            if not al[b]:continue
            be=list(al);be[a]+=1;be[b]-=1
            rr.append(bl[tuple(be)]);cc.append(col);vv.append(al[b])
        e[a,b]=sp.csr_matrix((vv,(rr,cc)),shape=(n,n),dtype=np.int64)
    I=sp.eye(N,format='csr',dtype=np.int64);i=sp.eye(n,format='csr',dtype=np.int64)
    Ctri=sum(E[a,b]@E[b,a]for a,b in it.product(range(d),repeat=2)).tocsr()
    qtri=((Ctri-(6*d+30)*I)@(Ctri-(6*d+10)*I)).tocsr()
    Cas=(sp.kron(Ctri,i)+2*(d+1)*sp.eye(N*n,format='csr',dtype=np.int64)
         +2*sum(sp.kron(E[a,b],e[b,a])for a,b in it.product(range(d),repeat=2))).tocsr()
    EM={a:(sp.kron(E[a,a+1],i)-sp.kron(I,e[a+1,a])).tocsr()for a in range(d-1)}
    pure=defaultdict(list);mixed=defaultdict(list)
    for a,b in it.product(range(N),range(n)):
        pure[tuple(sums[a][r]+bs[b][r]for r in range(d))].append((a,b))
        mixed[tuple(sums[a][r]-bs[b][r]for r in range(d))].append((a,b))
    highest=[]
    for wt,inds in mixed.items():
        if any(wt[r]<wt[r+1]for r in range(d-1)):continue
        ids=np.array([a*n+b for a,b in inds]);raises=[]
        for a in range(d-1):
            shift=list(wt);shift[a]+=1;shift[a+1]-=1
            dest=mixed.get(tuple(shift),[]);rid=np.array([u*n+v for u,v in dest],dtype=int)
            raises.append(EM[a][rid,:][:,ids].toarray())
        B=primitive_basis(S.Matrix(np.vstack(raises)))
        if not B.cols:continue
        highest.append((wt,inds,B))
        print('HW',wt,'rawsize',len(inds),'multiplicity',B.cols,flush=True)
    cache={};mapping={}
    def coordinate_map(order):
        if order not in mapping:
            qm=[bl[tuple(al[r]for r in order)]for al in bs]
            tm=[tl[tuple(sorted(qm[a]for a in t))]for t in triples]
            mapping[order]=(tm,qm)
        return mapping[order]
    def pure_gram(part):
        if part in cache:return cache[part]
        inds=pure[part];size=len(inds);loc={z:j for j,z in enumerate(inds)}
        ids=np.array([a*n+b for a,b in inds]);J=fm((Cas[ids,:][:,ids].toarray()-8*d*np.eye(size,dtype=np.int64)).tolist());Id=eye(size)
        R=fmpq_mat(size,size);P=fmpq_mat(size,size);Z=fmpq_mat(size,size)
        packs=[tuple(sorted(triples[a]+(b,)))for a,b in inds]
        mult=[math.prod(math.factorial(v)for v in Counter(z).values())for z in packs]
        for row,(a,b)in enumerate(inds):
            for col,(c,e0)in enumerate(inds):
                if packs[row]==packs[col]:R[row,col]=fmpq(orb[a]*mult[row],24)
                if b==e0:
                    if sums[a]==sums[c]:P[row,col]=fmpq(str(S.Rational(mf(sums[a]),90)/gt[a]))
                    Z[row,col]=fmpq(int(qtri[a,c]),576)
        D6=2*R*P*R-P*R-R*P
        D222=2*R*Z*R-Z*R-R*Z
        assert (J-28*Id)*D6==fmpq_mat(size,size),'D6 spectral support'
        assert (J-4*Id)*D222==fmpq_mat(size,size),'D222 spectral support'
        Q=poly(fp,J,Id)+poly(rp,J,Id)*R+fmpq(str(coeff[12]))*D6+fmpq(str(coeff[13]))*D222
        gram=fmpq_mat(size,size)
        for row,(a,b)in enumerate(inds):
            norm=fmpq(str(gt[a]*weights[b]))
            for col in range(size):gram[row,col]=norm*Q[row,col]
        assert gram==gram.transpose(),'Hermiticity'
        cache[part]=(gram,loc)
        print('PURE',part,'size',size,'seconds',round(time.time()-started,2),flush=True)
        return cache[part]
    records=[];allok=True
    for wt,inds,B in highest:
        M=fmpq_mat(len(inds),len(inds))
        for row,(a,b)in enumerate(inds):
            for col,(c,e0)in enumerate(inds):
                total=tuple(sums[a][r]+bs[e0][r]for r in range(d))
                order=tuple(sorted(range(d),key=lambda r:(-total[r],r)))
                part=tuple(total[r]for r in order);tm,qm=coordinate_map(order)
                Q,loc=pure_gram(part)
                M[row,col]=Q[loc[tm[a],qm[e0]],loc[tm[c],qm[b]]]
        assert M==M.transpose(),'mixed Hermiticity'
        BF=fm(B.tolist());HF=BF.transpose()*M*BF
        H=S.Matrix([[S.Rational(str(HF[r,c]))for c in range(HF.ncols())]for r in range(HF.nrows())])
        G=B.T*S.diag(*[gt[a]*weights[b]for a,b in inds])*B
        denominator=math.lcm(*[int(z.q)for z in H])
        ok,scaled_piv,err=exact_psd((denominator*H).tolist());allok &=ok
        piv=[str(S.Rational(z)/denominator)for z in scaled_piv]
        dim=S.prod(S.Rational(wt[r]-wt[s]+s-r,s-r)for r in range(d)for s in range(r+1,d))
        print('RESULT',wt,'dim',dim,'H',H.tolist(),'G',G.tolist(),'PSD',ok,'pivots',piv,flush=True)
        records.append({'weight':wt,'irrep_dimension':str(dim),'indices':inds,'basis':[[str(z)for z in row]for row in B.tolist()],
                        'H':[[str(z)for z in row]for row in H.tolist()],'G':[[str(z)for z in row]for row in G.tolist()],
                        'pivots':piv,'integer_scaling':denominator,'PSD':bool(ok),'error':err})
        if not ok:raise AssertionError((wt,err))
    out={'d':d,'coefficient_file':Path(coefpath).name,'coefficients':[str(z)for z in coeff],
         'casimir_offsets':OFF,'casimir_polynomial':[str(z)for z in fp],'R_polynomial':[str(z)for z in rp],
         'packet_basis':bs,'triple_basis':triples,'blocks':records,'all_PSD':bool(allok),
         'support_dimension':N*n,'canonical_pure_blocks':len(cache),'elapsed_seconds':time.time()-started}
    dest=Path(__file__).with_name(f'one_exact_d{d}.json');dest.write_text(json.dumps(out,indent=2))
    print('ALL EXACT ONE PSD',allok,'blocks',len(records),'file',dest,flush=True)

if __name__=='__main__':
    d=int(sys.argv[1])if len(sys.argv)>1 else 6
    path=sys.argv[2]if len(sys.argv)>2 else ROOT/f'rational38_d{d}.json'
    build(d,path)

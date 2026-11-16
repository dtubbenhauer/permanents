from check import comps,mf
from collections import Counter,defaultdict
from functools import lru_cache
from fractions import Fraction
import itertools as it,math,json,numpy as np,sys

def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def setup(d,k=2):
    bs=comps(k,d); pairs=list(it.combinations_with_replacement(range(len(bs)),2))
    sums=[add(bs[a],bs[b]) for a,b in pairs]
    groups=defaultdict(list)
    for i,s in enumerate(sums):
        for j,t in enumerate(sums):groups[sub(s,t)].append((i,j))
    @lru_cache(None)
    def data(u):
        al=[bs[i] for i in u];T=tuple(map(sum,zip(*al)))
        counts=Counter(add(al[i],al[j]) for i,j in it.combinations(range(4),2))
        h={s:mf(s)*mf(sub(T,s)) for s in counts}
        w=math.prod(mf(x) for x in al);mult=math.prod(math.factorial(n) for n in Counter(u).values())
        return T,counts,h,w*mult
    def entry(x,y):
        a,b=pairs[x[0]];c,e=pairs[x[1]]
        f,g=pairs[y[0]];h,j=pairs[y[1]]
        u=tuple(sorted((a,b,h,j)));v=tuple(sorted((f,g,c,e)))
        Tu,cu,hu,wu=data(u);Tv,cv,hv,wv=data(v)
        if Tu!=Tv:return 0
        su=sums[x[0]];sv=sums[y[0]]
        inner=sum(n*cv.get(s,0)*hu[s] for s,n in cu.items())
        return 4*mf(Tu)-4*(wu if u==v else 0)+inner-3*(cu.get(sv,0)*mf(sv)*mf(sub(Tu,sv))+cv.get(su,0)*mf(su)*mf(sub(Tu,su)))
    return bs,pairs,groups,entry

def exact_psd(A):
    n=len(A);B=[[Fraction(int(x)) for x in row] for row in A];piv=[]
    for i in range(n):
        p=B[i][i]
        if p<0:return False,piv,('negative',i,str(p))
        if p==0:
            if any(B[i][j] for j in range(i+1,n)):return False,piv,('zero_nonzero_row',i)
            piv.append('0');continue
        piv.append(str(p))
        for j in range(i+1,n):
            if not B[j][i]:continue
            v=B[j][i]/p
            for k in range(j,n):B[j][k]-=v*B[i][k];B[k][j]=B[j][k]
    return True,piv,None

def run(d,k=2,exact=True):
    bs,pairs,groups,entry=setup(d,k)
    print('dimension',d,'packetdim',len(bs),'pairdim',len(pairs),'total',len(pairs)**2,'groups',len(groups),'maxblock',max(map(len,groups.values())),'entries',sum(len(g)**2 for g in groups.values()),flush=True)
    results=[];worst=0
    for w,inds in groups.items():
        A=np.array([[entry(x,y) for y in inds] for x in inds],dtype=np.int64)
        if exact:
            ok,piv,err=exact_psd(A)
            if not ok: print('FAIL',w,err,'mineig',np.linalg.eigvalsh(A.astype(float))[0],flush=True);return False
            results.append({'weight':w,'indices':inds,'matrix':A.tolist(),'pivots':piv})
        else:
            e=np.linalg.eigvalsh(A.astype(float))[0];worst=min(worst,e)
            if e<-1e-7:print('NUMFAIL',w,e,'size',len(inds),flush=True);return False
    if exact:
        out=f'exact_k{k}_d{d}.json'
        with open(out,'w') as f:json.dump({'d':d,'k':k,'t':9*math.comb(2*k,k)**2/2,'packet_basis':bs,'pair_basis':pairs,'blocks':results},f)
        print('EXACT_PSD',d,k,'rank',sum(x!='0' for b in results for x in b['pivots']),'blocks',len(results),flush=True)
    else:print('NUMERIC_PSD',d,'worst',worst,flush=True)
    return True

if __name__=='__main__':
    run(int(sys.argv[1]) if len(sys.argv)>1 else 3,int(sys.argv[2]) if len(sys.argv)>2 and sys.argv[2].isdigit() else 2,exact='--numeric' not in sys.argv)

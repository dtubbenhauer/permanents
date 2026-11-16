"""Independent exact audits of the five-packet diagram and congruence data."""
import itertools as it
import math
from pathlib import Path
import random
import subprocess
import numpy as np
from fractions import Fraction as F

ROOT=Path(__file__).resolve().parent
M=5;NTHIN=10


def rep(D):
    used=[0]*5;p=[]
    for i in range(5):
        for j in range(5):
            for t in range(D[5*i+j]):p.append(2*j+used[j]);used[j]+=1
    return p


def orbit(D,ps):return {tuple(D[5*p[i]+p[j]] for i in range(5) for j in range(5)) for p in ps}


def cycles(p):
    used=set();n=0
    for i in range(10):
        if i in used:continue
        n+=1
        while i not in used:used.add(i);i=p[i]
    return n


def turn(i,cut):
    if 2*(5-cut)<=i<10:return i+10
    if 10+2*(5-cut)<=i<20:return i-10
    return i


def diagram(D,cut):
    A=[0]*20
    for i,j in enumerate(rep(D)):
        a,b=turn(i,cut),turn(10+j,cut);A[a]=b;A[b]=a
    return A


def compose(A,B,h):
    # Connected components, independent of the C++ alternating-path routine.
    graph=[[] for _ in range(40)]
    for i,j in enumerate(A):graph[i].append(j)
    for i,j in enumerate(B):graph[20+i].append(20+j)
    for i,j in enumerate(h):graph[10+i].append(20+j);graph[20+j].append(10+i)
    seen=set();out=[0]*20;loops=0
    for i in range(40):
        if i in seen:continue
        stack=[i];seen.add(i);ends=[]
        while stack:
            x=stack.pop()
            if x<10:ends.append(x)
            if x>=30:ends.append(x-20)
            for y in graph[x]:
                if y not in seen:seen.add(y);stack.append(y)
        if not ends:loops+=1
        else:
            assert len(ends)==2
            out[ends[0]]=ends[1];out[ends[1]]=ends[0]
    return out,loops


def load(cut):
    with open(ROOT/f'five_packet_density_cut{cut}_d8.bin','rb') as f:
        m,k,d,c,N,NG,h,NF=map(int,np.fromfile(f,np.int32,8));assert (m,k,d,c)==(5,2,8,cut)
        Ds=np.fromfile(f,np.int32,N*25).reshape(N,25);gDs=np.fromfile(f,np.int32,NG*25).reshape(NG,25)
        sizes=np.fromfile(f,np.int32,N);gsizes=np.fromfile(f,np.int32,NG)
        star=np.fromfile(f,np.int32,N);gstar=np.fromfile(f,np.int32,NG)
        trace=np.fromfile(f,np.int64,N);gram=np.fromfile(f,np.int64,N*N).reshape(N,N)
        matrices=np.fromfile(f,np.int32,NG*N*N).reshape(NG,N,N)
    return Ds,gDs,sizes,gsizes,star,gstar,trace,gram,matrices


def audit_diagrams():
    rng=random.Random(311221);P=list(it.permutations(range(5)))
    H=[[i^((mask>>(i//2))&1) for i in range(10)] for mask in range(32)]
    rows=[r for r in it.product(range(3),repeat=5) if sum(r)==2]
    full=[]
    def visit(prefix,remaining):
        if len(prefix)==4:
            if sum(remaining)==2:full.append(tuple(v for r in prefix+[remaining] for v in r))
            return
        for row in rows:
            rest=tuple(a-b for a,b in zip(remaining,row))
            if min(rest)>=0:visit(prefix+[row],rest)
    visit([], (2,)*5);assert len(full)==6210
    for cut in [0,1,2]:
        Ds,gDs,sizes,gsizes,star,gstar,trace,G,T=load(cut)
        ps=[p for p in P if all((i<5-cut)==(p[i]<5-cut) for i in range(5))]
        index={tuple(D):i for i,D in enumerate(Ds)}
        lookup={D:index[min(orbit(D,ps))] for D in full}
        for i,D in enumerate(Ds):
            p=rep(D);expected=sum(8**cycles([p[h[j]] for j in range(10)]) for h in H)
            assert expected==trace[i]
        for _ in range(8):
            g=rng.randrange(len(gDs));j=rng.randrange(len(Ds));expected=[0]*len(Ds)
            for D in orbit(gDs[g],P):
                A=diagram(D,cut);B=diagram(Ds[j],cut)
                for h in H:
                    C,loops=compose(A,B,h);out=[0]*25
                    for i in range(10):
                        t=turn(C[turn(i,cut)],cut)-10;assert 0<=t<10
                        out[(i//2)*5+t//2]+=1
                    expected[lookup[tuple(out)]]+=8**loops
            assert expected==list(T[g,:,j])
        for _ in range(4):
            i=rng.randrange(len(Ds));j=rng.randrange(len(Ds));pe=rep(Ds[j]);total=0
            for D in orbit(Ds[i],ps):
                pd=rep(D);inverse=[0]*10
                for a,b in enumerate(pd):inverse[b]=a
                for h in H:
                    q=[pe[h[inverse[t]]] for t in range(10)]
                    for h0 in H:total+=8**cycles([q[h0[t]] for t in range(10)])
            assert total==int(G[i,j]),(cut,i,j,total,int(G[i,j]))
        print('cut',cut,': every trace, eight left-action columns, four unbent group-trace Gram checks: EXACT PASS',flush=True)


def audit_congruence_rows():
    rng=random.Random(6159)
    for cut in [0,1,2]:
        Ds,gDs,sizes,gsizes,star,gstar,tr,gn,M=load(cut);n=len(Ds)
        with open(ROOT/f'five_packet_ppt_witness_cut{cut}.bin','rb') as f:
            h=np.fromfile(f,np.int64,4);z=np.fromfile(f,np.int64,len(gDs));R=np.fromfile(f,np.int64,n*n).reshape(n,n)
        lcm=math.lcm(*map(int,sizes));G=gn.astype(object)*(lcm//sizes.astype(object))[:,None]
        assert int(max(abs(z)))*int(np.max(abs(M)))*len(gDs)<2**63
        L=np.einsum('a,aij->ij',z,M.astype(np.int64)).astype(object)
        R=R.astype(object)
        selected=list(range(n)) if cut==0 else sorted({0,n-1,*[rng.randrange(n) for _ in range(10)]})
        for i in selected:
            row=((R[i]@G)@L)@R.T
            assert row[i]>sum(abs(row[j]) for j in range(n) if j!=i)
        print('cut',cut,':',len(selected),'congruence rows independently recomputed with Python integers: EXACT PASS',flush=True)


def audit_arithmetic():
    rng=random.Random(9181);rows=[];expected=[];mask=(1<<64)-1
    for i in range(400):
        a=rng.getrandbits(126);a=-a if rng.randrange(2) else a
        b=rng.getrandbits(180 if i%3 else 230);b=-b if rng.randrange(2) else b
        r=rng.randrange(-(1<<50),1<<50);s=rng.randrange(-1000,1000) if i%3 else rng.choice([-1,1])
        if i%17==0:b=-a*r
        aa,bb=abs(a),abs(b)
        rows.append(' '.join(map(str,[aa&mask,aa>>64,int(a<0),r,*[(bb>>(64*j))&mask for j in range(4)],int(b<0),s])))
        expected.append((a*r+b)*s)
    result=subprocess.run([str(ROOT/'verify_five_packet_ppt'),'--arithmetic-audit'],
            input=str(len(rows))+'\n'+'\n'.join(rows)+'\n',capture_output=True,text=True,check=True)
    assert len(result.stdout.splitlines())==len(expected)
    for line,x in zip(result.stdout.splitlines(),expected):
        bits=list(map(int,line.split()));v=sum(a<<(64*j) for j,a in enumerate(bits[1:]));v=-v if bits[0] else v
        assert x==v
    print('400 signed 256-bit operations independently checked against Python: EXACT PASS',flush=True)


if __name__ == "__main__":
    audit_arithmetic()
    audit_diagrams()
    audit_congruence_rows()

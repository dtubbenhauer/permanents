#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <unordered_map>
#include <vector>

// Direct left actions of globally invariant densities. No dense N^3 table.
constexpr int m=5,k=2,n=10,h=32;
using Flow=std::array<int,m*m>;
using Perm=std::array<int,n>;
using Pair=std::array<int,2*n>;
using Pack=std::array<int,m>;
uint64_t encode(const Flow&D){uint64_t z=0;for(int i=0;i<m*m;++i)z|=uint64_t(D[i])<<(2*i);return z;}
Flow conjugate(const Flow&D,const Pack&p){Flow E;for(int i=0;i<m;++i)for(int j=0;j<m;++j)E[m*i+j]=D[m*p[i]+p[j]];return E;}
Flow transpose(const Flow&D){Flow E;for(int i=0;i<m;++i)for(int j=0;j<m;++j)E[m*i+j]=D[m*j+i];return E;}
Perm representative(const Flow&D){Perm p;std::array<int,m>used={};int pos=0;for(int i=0;i<m;++i)for(int j=0;j<m;++j)for(int t=0;t<D[m*i+j];++t)p[pos++]=k*j+used[j]++;return p;}
int cycles(const Perm&p){bool used[n]={};int ans=0;for(int i=0;i<n;++i)if(!used[i]){++ans;int j=i;while(!used[j]){used[j]=true;j=p[j];}}return ans;}
template<class T>void write(std::ofstream&out,const std::vector<T>&a){out.write((const char*)a.data(),a.size()*sizeof(T));}

int main(int argc,char**argv){
 if(argc!=4){std::cerr<<"cut dimension output\n";return 2;}
 int cut=std::stoi(argv[1]),d=std::stoi(argv[2]);
 std::vector<Pack> allpack,subpack;Pack p={0,1,2,3,4};
 do{allpack.push_back(p);bool good=true;for(int i=0;i<m;++i)if((i<m-cut)!=(p[i]<m-cut))good=false;if(good)subpack.push_back(p);}while(std::next_permutation(p.begin(),p.end()));
 std::vector<Flow> flows;Flow D={};std::array<int,m>remaining;remaining.fill(k);
 auto rec=[&](auto&&self,int pos,int rowleft)->void{
  if(pos==m*m){flows.push_back(D);return;}
  int i=pos/m,j=pos%m,lo=0,hi=std::min(rowleft,remaining[j]);
  if(i==m-1)lo=hi=remaining[j];if(j==m-1)lo=hi=rowleft;
  if(lo<0||hi>remaining[j]||hi>rowleft)return;
  for(int v=lo;v<=hi;++v){D[pos]=v;remaining[j]-=v;if(j==m-1){if(rowleft==v)self(self,pos+1,k);}else self(self,pos+1,rowleft-v);remaining[j]+=v;}
 };rec(rec,0,k);
 std::map<Flow,int> globalidx,cutidx;
 std::vector<Flow> gc,bc;
 for(const auto&F:flows){Flow a=F,b=F;for(const auto&p:allpack)a=std::min(a,conjugate(F,p));for(const auto&p:subpack)b=std::min(b,conjugate(F,p));gc.push_back(a);bc.push_back(b);globalidx[a]=0;cutidx[b]=0;}
 std::vector<Flow> globalreps,reps;int pos=0;for(auto&v:globalidx){v.second=pos++;globalreps.push_back(v.first);}pos=0;for(auto&v:cutidx){v.second=pos++;reps.push_back(v.first);}
 int N=reps.size(),NG=globalreps.size(),NF=flows.size();
 std::vector<int32_t> globalid(NF),basisid(NF),sizes(N),gsizes(NG),star(N),gstar(NG);
 std::unordered_map<uint64_t,int> codes;codes.reserve(10000);
 for(int i=0;i<NF;++i){globalid[i]=globalidx.at(gc[i]);basisid[i]=cutidx.at(bc[i]);++sizes[basisid[i]];++gsizes[globalid[i]];codes[encode(flows[i])]=basisid[i];}
 auto canon=[&](const Flow&F,const std::vector<Pack>&ps){Flow a=F;for(const auto&p:ps)a=std::min(a,conjugate(F,p));return a;};
 for(int i=0;i<N;++i)star[i]=cutidx.at(canon(transpose(reps[i]),subpack));
 for(int i=0;i<NG;++i)gstar[i]=globalidx.at(canon(transpose(globalreps[i]),allpack));
 std::array<int64_t,n+1>power;power[0]=1;for(int i=1;i<=n;++i)power[i]=power[i-1]*d;
 std::vector<int64_t> traces(N);
 for(int i=0;i<N;++i){auto r=representative(reps[i]);for(int mask=0;mask<h;++mask){Perm q;for(int j=0;j<n;++j)q[j]=r[j^((mask>>(j/k))&1)];traces[i]+=power[cycles(q)];}}
 auto turn=[&](int a){if((m-cut)*k<=a&&a<n)return a+n;if(n+(m-cut)*k<=a&&a<2*n)return a-n;return a;};
 auto diagram=[&](const Flow&F){Pair A;auto p=representative(F);for(int i=0;i<n;++i){int a=turn(i),b=turn(n+p[i]);A[a]=b;A[b]=a;}return A;};
 std::vector<Pair> As,Bs;for(const auto&F:flows)As.push_back(diagram(F));for(const auto&F:reps)Bs.push_back(diagram(F));
 std::vector<Perm> thin(h);for(int mask=0;mask<h;++mask)for(int i=0;i<n;++i)thin[mask][i]=i^((mask>>(i/k))&1);
 std::vector<int32_t> matrices((size_t)NG*N*N,0);
 std::vector<int64_t> gram((size_t)N*N,0);
 auto start=std::chrono::steady_clock::now();
 std::cerr<<"cut="<<cut<<" full="<<NF<<" N="<<N<<" NG="<<NG<<"\n";
 for(int j=0;j<N;++j){auto B=Bs[j];
  for(int a=0;a<NF;++a){auto A=As[a];int gi=globalid[a],bi=star[basisid[a]];
   for(auto p:thin){
    int edge[4*n],mid[4*n];bool used[4*n]={};
    for(int i=0;i<2*n;++i){edge[i]=A[i];edge[2*n+i]=2*n+B[i];mid[i]=mid[2*n+i]=-1;}
    for(int i=0;i<n;++i){mid[n+i]=2*n+p[i];mid[2*n+p[i]]=n+i;}
    Pair C;int loops=0;
    for(int s=0;s<4*n;++s){
     if(used[s]||(s>=n&&s<3*n))continue;
     int x=s,prev=-1,other=-1;
     while(true){used[x]=true;int y=edge[x]!=prev?edge[x]:mid[x];if(y<0){other=x;break;}prev=x;x=y;}
     int u=s<n?s:s-2*n,v=other<n?other:other-2*n;C[u]=v;C[v]=u;
    }
    for(int s=n;s<3*n;++s){if(used[s])continue;++loops;int x=s,prev=-1;do{used[x]=true;int y=edge[x]!=prev?edge[x]:mid[x];prev=x;x=y;}while(x!=s);}
    uint64_t code=0;
    for(int i=0;i<n;++i){int col=(turn(C[turn(i)])-n)/k;code+=uint64_t(1)<<(2*((i/k)*m+col));}
    auto found=codes.find(code);if(found==codes.end()){std::cerr<<"bad flow\n";return 3;}int c=found->second;
    matrices[((size_t)gi*N+c)*N+j]+=int32_t(power[loops]);
    gram[(size_t)bi*N+j]+=power[loops]*traces[c];
   }
  }
  if(j%10==0||j+1==N)std::cerr<<j+1<<"/"<<N<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"\n";
 }
 std::ofstream out(argv[3],std::ios::binary);int32_t header[8]={m,k,d,cut,N,NG,h,NF};out.write((const char*)header,sizeof(header));
 for(auto F:reps)out.write((const char*)F.data(),sizeof(F));for(auto F:globalreps)out.write((const char*)F.data(),sizeof(F));
 write(out,sizes);write(out,gsizes);write(out,star);write(out,gstar);write(out,traces);write(out,gram);write(out,matrices);
 return !out;
}

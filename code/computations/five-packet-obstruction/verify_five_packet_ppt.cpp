#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using I128=__int128_t;
using U128=__uint128_t;
// Signed magnitude, four 64-bit limbs. Only addition and multiplication by
// a signed 64-bit integer are needed. Every carry beyond 256 bits aborts.
struct Big{
 std::array<uint64_t,4>w={};bool negative=false;
 Big()=default;
 Big(I128 x){negative=x<0;U128 u=x<0?U128(-x):U128(x);w[0]=uint64_t(u);w[1]=uint64_t(u>>64);}
 bool zero()const{return !(w[0]|w[1]|w[2]|w[3]);}
 int magcompare(const Big&b)const{for(int i=3;i>=0;--i)if(w[i]!=b.w[i])return w[i]<b.w[i]?-1:1;return 0;}
 Big&operator+=(const Big&b){
  if(negative==b.negative){U128 carry=0;for(int i=0;i<4;++i){U128 x=U128(w[i])+b.w[i]+carry;w[i]=uint64_t(x);carry=x>>64;}if(carry)throw std::runtime_error("256-bit addition overflow");}
  else{int c=magcompare(b);const auto&a=c>=0?w:b.w;const auto&v=c>=0?b.w:w;std::array<uint64_t,4>out;uint64_t borrow=0;for(int i=0;i<4;++i){U128 sub=U128(v[i])+borrow;out[i]=a[i]-uint64_t(sub);borrow=U128(a[i])<sub;}if(borrow)throw std::runtime_error("invalid magnitude subtraction");w=out;if(c<0)negative=b.negative;}
  if(zero())negative=false;return *this;
 }
 Big times(int64_t b)const{Big out;out.negative=negative!=(b<0);uint64_t u=b<0?uint64_t(-b):uint64_t(b);U128 carry=0;for(int i=0;i<4;++i){U128 x=U128(w[i])*u+carry;out.w[i]=uint64_t(x);carry=x>>64;}if(carry)throw std::runtime_error("256-bit multiplication overflow");if(out.zero())out.negative=false;return out;}
 bool operator<(const Big&b)const{if(negative!=b.negative)return negative;int c=magcompare(b);return negative?c>0:c<0;}
 bool operator<=(const Big&b)const{return !(b<*this);}
 long double floating()const{long double x=0;for(int i=3;i>=0;--i)x=x*18446744073709551616.L+w[i];return negative?-x:x;}
};
Big operator+(Big a,const Big&b){a+=b;return a;}
Big operator-(Big a,Big b){if(!b.zero())b.negative=!b.negative;a+=b;return a;}
Big ab(Big a){a.negative=false;return a;}
int bits(uint64_t x){int n=0;while(x){++n;x>>=1;}return n;}
std::string decimal(I128 x){bool neg=x<0;U128 u=neg?U128(-x):U128(x);std::string s;do{s.push_back('0'+u%10);u/=10;}while(u);if(neg)s.push_back('-');std::reverse(s.begin(),s.end());return s;}
template<class T>std::vector<T> read(std::ifstream&f,size_t n){std::vector<T>a(n);f.read((char*)a.data(),n*sizeof(T));if(!f)throw std::runtime_error("truncated input");return a;}
template<class T>T ab(T x){return x<0?-x:x;}
int main(int argc,char**argv){
 if(argc==2&&std::string(argv[1])=="--arithmetic-audit"){
  int cases;std::cin>>cases;for(int t=0;t<cases;++t){Big a,b;int na,nb;int64_t r,s;std::cin>>a.w[0]>>a.w[1]>>na>>r;for(int j=0;j<4;++j)std::cin>>b.w[j];std::cin>>nb>>s;a.negative=na&&!a.zero();b.negative=nb&&!b.zero();Big out=(a.times(r)+b).times(s);std::cout<<out.negative;for(auto v:out.w)std::cout<<' '<<v;std::cout<<'\n';}return 0;
 }
 if(argc!=3){std::cerr<<"algebra_file witness_file\n";return 2;}
 std::ifstream f(argv[1],std::ios::binary),w(argv[2],std::ios::binary);
 auto h=read<int32_t>(f,8);int m=h[0],k=h[1],d=h[2],cut=h[3],N=h[4],NG=h[5],thin=h[6];
 if(m!=5||k!=2||d!=8||NG!=85||thin!=32)throw std::runtime_error("unexpected header");
 auto Ds=read<int32_t>(f,N*25),gDs=read<int32_t>(f,NG*25),sizes=read<int32_t>(f,N),gsizes=read<int32_t>(f,NG),star=read<int32_t>(f,N),gstar=read<int32_t>(f,NG);
 auto traces=read<int64_t>(f,N),gn=read<int64_t>(f,(size_t)N*N);
 auto M=read<int32_t>(f,(size_t)NG*N*N);
 auto wh=read<int64_t>(w,4);if(wh[0]!=N||wh[1]!=NG||wh[2]<=0||wh[3]<=0)throw std::runtime_error("bad witness header");
 auto z=read<int64_t>(w,NG),R=read<int64_t>(w,(size_t)N*N);
 for(int i=0;i<NG;++i)if(z[i]!=z[gstar[i]])throw std::runtime_error("density not self-adjoint");
 int64_t orbitlcm=1;for(auto s:sizes)orbitlcm=std::lcm(orbitlcm,int64_t(s));
 std::vector<int64_t>G((size_t)N*N),L((size_t)N*N);int64_t maxG=0,maxL=0,maxR=0;
 for(int i=0;i<N;++i)for(int j=0;j<N;++j){
  I128 v=I128(gn[(size_t)i*N+j])*(orbitlcm/sizes[i]);if(ab(v)>INT64_MAX)throw std::runtime_error("Gram overflow");G[(size_t)i*N+j]=int64_t(v);maxG=std::max(maxG,ab(int64_t(v)));
  I128 a=0;for(int b=0;b<NG;++b)a+=I128(z[b])*M[((size_t)b*N+i)*N+j];if(ab(a)>INT64_MAX)throw std::runtime_error("left action overflow");L[(size_t)i*N+j]=int64_t(a);maxL=std::max(maxL,ab(int64_t(a)));
  if(j>i&&R[(size_t)i*N+j])throw std::runtime_error("congruence not triangular");
  maxR=std::max(maxR,ab(R[(size_t)i*N+j]));
 }
 for(int i=0;i<N;++i){if(!R[(size_t)i*N+i])throw std::runtime_error("singular congruence");for(int j=0;j<N;++j)if(G[(size_t)i*N+j]!=G[(size_t)j*N+i])throw std::runtime_error("Gram not symmetric");}
 int hbits=bits(N)+bits(maxG)+bits(maxL);if(hbits>=126)throw std::runtime_error("128-bit multiplication bound failed");
 int kbits=2*bits(N)+2*bits(maxR)+hbits;if(kbits>=250)throw std::runtime_error("256-bit multiplication bound failed");
 std::vector<I128>H((size_t)N*N);
 for(int i=0;i<N;++i)for(int j=0;j<=i;++j){I128 a=0,b=0;for(int t=0;t<N;++t){a+=I128(G[(size_t)i*N+t])*L[(size_t)t*N+j];b+=I128(G[(size_t)j*N+t])*L[(size_t)t*N+i];}if(a!=b)throw std::runtime_error("exact self-adjointness failed");H[(size_t)i*N+j]=H[(size_t)j*N+i]=a;}
 std::vector<Big>Q((size_t)N*N),diagonal(N),off(N);
 for(int i=0;i<N;++i)for(int t=0;t<=i;++t){int64_t r=R[(size_t)i*N+t];if(!r)continue;for(int j=0;j<N;++j)Q[(size_t)i*N+j]+=Big(H[(size_t)t*N+j]).times(r);}
 for(int i=0;i<N;++i)for(int j=0;j<=i;++j){Big a;for(int t=0;t<=j;++t)a+=Q[(size_t)i*N+t].times(R[(size_t)j*N+t]);if(i==j)diagonal[i]=a;else{off[i]+=ab(a);off[j]+=ab(a);}}
 long double minratio=2;
 for(int i=0;i<N;++i){if(diagonal[i]<=off[i])throw std::runtime_error("exact strict diagonal dominance FAILED");long double r=(diagonal[i]-off[i]).floating()/diagonal[i].floating();minratio=std::min(minratio,r);}
 std::cout<<"cut="<<cut<<" N="<<N<<" exact self-adjointness, nonsingular rational congruence and strict diagonal dominance: EXACT PASS; display-only relative margin="<<minratio<<"\n";
 if(cut==0){
  int64_t maxz=0,maxsize=0;for(auto a:z)maxz=std::max(maxz,ab(a));for(auto a:sizes)maxsize=std::max(maxsize,int64_t(a));if(2*bits(N)+bits(maxz)+2*bits(maxsize)+bits(maxG)+6>=126)throw std::runtime_error("pairing bound failed");
  I128 numerator=0;for(int i=0;i<N;++i)for(int j=0;j<N;++j){int twos=0;bool pure=true;for(int t=0;t<25;++t){twos+=Ds[25*j+t]==2;if(Ds[25*j+t]==1)pure=false;}int x=32/(1<<twos)-int(pure);numerator+=I128(z[i])*sizes[i]*G[(size_t)i*N+j]*x*sizes[j];}
  if(numerator>=0)throw std::runtime_error("separation pairing not negative");
  I128 denominator=I128(wh[2])*orbitlcm*thin*thin;for(int j=0;j<5;++j)denominator*=36;
  std::cout<<"Normalized trace pairing = "<<decimal(numerator)<<" / "<<decimal(denominator)<<" < 0: EXACT PASS\n";
 }
 return 0;
}

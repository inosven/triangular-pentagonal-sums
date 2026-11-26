// Exhaustive check of Theorem E: N=24n+7 > 7. For every primitive triple (v,a,b) of S(N), the walk
// alpha,beta,alpha,... from it reaches a triple with (v≡2 mod 3 or v=1) and a≠b.
// Also reports the non-primitive starting triples from which no such triple is reached.
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll isq(ll n){ ll r=(ll)sqrt((double)n); while(r*r>n) r--; while((r+1)*(r+1)<=n) r++; return r;}
static ll g(ll a,ll b){ while(b){ll t=a%b;a=b;b=t;} return a; }
static void phi(ll u,ll v,ll*u2,ll*v2){ if(((u-v)%4+4)%4==0){ *u2=(u+v)/2; *v2=(v<3*u)?(3*u-v)/2:(v-3*u)/2; } else { *u2=llabs(u-v)/2; *v2=(3*u+v)/2; } }
static int good(ll v,ll a,ll b){ return (v%3==2||v==1)&&a!=b; }
int main(int argc,char**argv){ ll M=atoll(argv[1]); ll nprim=0,maxw=0,nnonprim_stuck=0; int shown=0;
  for(ll n=1;n<M;n++){ ll N=24*n+7;
    for(ll a=1;3*a*a<N;a+=2) for(ll b=1;3*a*a+3*b*b<N;b+=2){ ll r=N-3*a*a-3*b*b; ll v=isq(r); if(v*v!=r||!(v&1)) continue;
      int prim=(g(g(v,a),b)==1);
      ll cv=v,ca=a,cb=b; int turn=0; ll steps=0; int ok=0;
      for(;;){ if(good(cv,ca,cb)){ok=1;break;}
        ll x2,v2; if(turn==0){ phi(ca,cv,&x2,&v2); ca=x2; cv=v2; } else { phi(cb,cv,&x2,&v2); cb=x2; cv=v2; } turn^=1; steps++;
        if(cv==v&&ca==a&&cb==b&&turn==0) break; if(steps>10000000){ printf("no return N=%lld\n",N); return 1; } }
      if(prim){ nprim++; if(!ok){ printf("FAIL: primitive (%lld,%lld,%lld) N=%lld\n",v,a,b,N); return 1; } if(steps>maxw) maxw=steps; }
      else if(!ok){ nnonprim_stuck++; if(shown<12){ ll d=g(g(v,a),b); printf("  non-primitive without good triple: (%lld,%lld,%lld) = %lld*(%lld,%lld,%lld), N=%lld\n",v,a,b,d,v/d,a/d,b/d,N); shown++; } } } }
  printf("n<%lld: every primitive triple (%lld of them) reaches a good triple, after at most %lld steps; %lld non-primitive triples do not. OK\n",M,nprim,maxw,nnonprim_stuck); }

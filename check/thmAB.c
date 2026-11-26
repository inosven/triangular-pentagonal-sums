// Exhaustive check of Theorems A and B (the descent), for every all-odd state.
// A: N=24n+7 = v^2+3a^2+3b^2, v,a,b odd positive. From every state not all equal, the alternating walk
//    alpha,beta,alpha,... reaches a state of the other class (v mod 3). Also checks: partner map is an involution,
//    preserves N, oddness, positivity, 3∤v; flip <=> not(a≡v mod 4 and v<3a).
// B: N=24n+5 = 3u^2+v^2+w^2. From every state not all equal with v≡w mod 3, the walk reaches v≢w mod 3.
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
static long long isq(long long n){ long long r=(long long)sqrt((double)n); while(r*r>n) r--; while((r+1)*(r+1)<=n) r++; return r;}
typedef long long ll;
static void die(const char*m,ll N,ll x,ll y,ll z){ printf("FAIL %s N=%lld (%lld,%lld,%lld)\n",m,N,x,y,z); exit(1);} 
// partner of (u,v) for 3u^2+v^2
static void phi(ll u,ll v,ll*u2,ll*v2,int*flip){
  if(((u-v)%4+4)%4==0){ *u2=(u+v)/2; if(v<3*u){*v2=(3*u-v)/2;*flip=0;} else {*v2=(v-3*u)/2;*flip=1;} }
  else { *u2=llabs(u-v)/2; *v2=(3*u+v)/2; *flip=1; } }
static void chk(ll u,ll v,ll u2,ll v2,int flip,ll N,ll c){
  if(3*u2*u2+v2*v2!=3*u*u+v*v) die("norm",N,u,v,c);
  if(!(u2&1)||!(v2&1)||u2<=0||v2<=0||v2%3==0) die("odd/pos",N,u,v,c);
  if(flip!=((v%3)!=(v2%3))) die("flipclass",N,u,v,c);
  ll u3,v3;int f3; phi(u2,v2,&u3,&v3,&f3); if(u3!=u||v3!=v) die("involution",N,u,v,c); }
int main(int argc,char**argv){ ll M=atoll(argv[1]); ll maxA=0,maxB=0,nA=0,nB=0;
  for(ll n=0;n<M;n++){
    ll N=24*n+7;
    for(ll a=1;3*a*a<N;a+=2) for(ll b=1;3*a*a+3*b*b<N;b+=2){ ll r=N-3*a*a-3*b*b; ll v=isq(r); if(v*v!=r||!(v&1)) continue;
      if(v%3==0) die("3|v",N,v,a,b);
      nA++; if(v==a&&a==b) continue;
      ll cv=v,ca=a,cb=b; int c0=v%3; ll steps=0; int turn=0;
      while(cv%3==c0){ ll x2,v2;int f; if(turn==0){ phi(ca,cv,&x2,&v2,&f); chk(ca,cv,x2,v2,f,N,cb); ca=x2; cv=v2; } else { phi(cb,cv,&x2,&v2,&f); chk(cb,cv,x2,v2,f,N,ca); cb=x2; cv=v2; }
        turn^=1; if(++steps>1000000) die("A no termination",N,v,a,b); }
      if(cv*cv+3*ca*ca+3*cb*cb!=N) die("A norm",N,v,a,b);
      if(steps>maxA) maxA=steps; }
    N=24*n+5;
    for(ll u=1;3*u*u<N;u+=2) for(ll v=1;3*u*u+v*v<N;v+=2){ ll r=N-3*u*u-v*v; ll w=isq(r); if(w*w!=r||!(w&1)) continue;
      if(v%3==0||w%3==0) die("3|vw",N,u,v,w);
      nB++; if(u==v&&v==w) continue;
      ll cu=u,cv=v,cw=w; ll steps=0; int turn=0;
      while(cv%3==cw%3){ ll x2,v2;int f; if(turn==0){ phi(cu,cv,&x2,&v2,&f); chk(cu,cv,x2,v2,f,N,cw); cu=x2; cv=v2; } else { phi(cu,cw,&x2,&v2,&f); chk(cu,cw,x2,v2,f,N,cv); cu=x2; cw=v2; }
        turn^=1; if(++steps>1000000) die("B no termination",N,u,v,w); }
      if(3*cu*cu+cv*cv+cw*cw!=N) die("B norm",N,u,v,w);
      if(steps>maxB) maxB=steps; } }
  printf("n<%lld: Theorem A checked on %lld states (max walk %lld); Theorem B on %lld states (max walk %lld). OK\n",M,nA,maxA,nB,maxB); }

// Exhaustive check of two refinements of Theorems 3.2 and 3.3.
// C: N=24n+7, S(N)={(v,a,b) odd positive, v^2+3a^2+3b^2=N}. From every non-diagonal state the walk
//    alpha,beta,alpha,... reaches (i) a state with v≡1 mod 3 and v>1, or (ii) a state with v=1 and (a=1 or b=1).
//    Before that, every step is the linear map A' (resp. B') on (vt,a,b), vt = v if v≡1 mod 3 else -v:
//    vt' = -(3a+vt)/2, a' = (a-vt)/2.
//    From a state of kind (ii): N in {7,31}, or one or two explicit steps give a state of kind (i).
// D: N=24n+5, T(N)={(u,v,w) odd positive, 3u^2+v^2+w^2=N}. Signed vt,wt ≡ 1 mod 3.
//    good: (vt>=4 and wt<=1) or (wt>=4 and vt<=1). From every non-diagonal state the walk reaches a good state
//    or a state with u=1 and (v=1 or w=1); before that all states have both >=4 (steps are A,B) or both <=1 (steps A',B').
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static ll isq(ll n){ ll r=(ll)sqrt((double)n); while(r*r>n) r--; while((r+1)*(r+1)<=n) r++; return r;}
static void die(const char*m,ll N,ll x,ll y,ll z){ printf("FAIL %s N=%lld (%lld,%lld,%lld)\n",m,N,x,y,z); exit(1);}
static void phi(ll u,ll v,ll*u2,ll*v2){ if(((u-v)%4+4)%4==0){ *u2=(u+v)/2; *v2=(v<3*u)?(3*u-v)/2:(v-3*u)/2; } else { *u2=llabs(u-v)/2; *v2=(3*u+v)/2; } }
static ll sg(ll v){ return (v%3==1)?v:-v; }
static int goodC(ll v){ return v%3==1 && v>1; }
static int goodD(ll v,ll w){ ll vt=sg(v),wt=sg(w); return (vt>=4&&wt<=1)||(wt>=4&&vt<=1); }
int main(int argc,char**argv){ ll M=atoll(argv[1]); ll nC=0,nD=0,maxC=0,maxD=0,exC=0,exD=0;
  for(ll n=0;n<M;n++){
    ll N=24*n+7;
    for(ll a=1;3*a*a<N;a+=2) for(ll b=1;3*a*a+3*b*b<N;b+=2){ ll r=N-3*a*a-3*b*b; ll v=isq(r); if(v*v!=r||!(v&1)) continue;
      nC++; if(v==a&&a==b) continue;
      ll cv=v,ca=a,cb=b; ll steps=0; int turn=0;
      while(!goodC(cv) && !(cv==1&&(ca==1||cb==1))){
        ll vt=sg(cv); if(vt>1) die("C: state with vt>1 not good",N,cv,ca,cb);
        ll x2,v2; if(turn==0){ phi(ca,cv,&x2,&v2); if(sg(v2)!=-(3*ca+vt)/2 && !goodC(v2)) die("C: step not A'",N,cv,ca,cb); if(!goodC(v2) && x2!=(ca-vt)/2) die("C: a' not A'",N,cv,ca,cb); ca=x2; cv=v2; }
        else { phi(cb,cv,&x2,&v2); if(sg(v2)!=-(3*cb+vt)/2 && !goodC(v2)) die("C: step not B'",N,cv,ca,cb); if(!goodC(v2) && x2!=(cb-vt)/2) die("C: b' not B'",N,cv,ca,cb); cb=x2; cv=v2; }
        turn^=1; if(++steps>1000000) die("C no termination",N,v,a,b); }
      if(steps>maxC) maxC=steps;
      if(!goodC(cv)){ exC++; // kind (ii): (1,1,b) or (1,a,1)
        ll o=(ca==1)?cb:ca; int other_is_b=(ca==1);
        if(o==1){ if(N!=7) die("C (1,1,1)",N,cv,ca,cb); }
        else if(o%4==1){ ll x2,v2; phi(o,1,&x2,&v2); if(!goodC(v2)) die("C ex 1 step",N,cv,ca,cb); }
        else if(o==3){ if(N!=31) die("C b=3",N,cv,ca,cb); }
        else { ll x2,v2,y2,v3; phi(o,1,&x2,&v2); phi(1,v2,&y2,&v3); if(!goodC(v3)) die("C ex 2 steps",N,cv,ca,cb); (void)other_is_b; } } }
    N=24*n+5;
    for(ll u=1;3*u*u<N;u+=2) for(ll v=1;3*u*u+v*v<N;v+=2){ ll r=N-3*u*u-v*v; ll w=isq(r); if(w*w!=r||!(w&1)) continue;
      nD++; if(u==v&&v==w) continue;
      ll cu=u,cv=v,cw=w; ll steps=0; int turn=0;
      while(!goodD(cv,cw) && !(cu==1&&(cv==1||cw==1))){
        ll vt=sg(cv),wt=sg(cw); int P=(vt>=4&&wt>=4), Mm=(vt<=1&&wt<=1); if(!P&&!Mm) die("D: bad state in neither region",N,cu,cv,cw);
        ll x2,v2; if(turn==0){ phi(cu,cv,&x2,&v2); ll nv=sg(v2);
            if(!goodD(v2,cw)){ if(P){ if(!(nv==(3*cu-vt)/2 && x2==(cu+vt)/2)) die("D: step not A in P",N,cu,cv,cw); } else { if(!(nv==-(3*cu+vt)/2 && x2==(cu-vt)/2)) die("D: step not A' in M",N,cu,cv,cw); } }
            cu=x2; cv=v2; }
        else { phi(cu,cw,&x2,&v2); ll nv=sg(v2);
            if(!goodD(cv,v2)){ if(P){ if(!(nv==(3*cu-wt)/2 && x2==(cu+wt)/2)) die("D: step not B in P",N,cu,cv,cw); } else { if(!(nv==-(3*cu+wt)/2 && x2==(cu-wt)/2)) die("D: step not B' in M",N,cu,cv,cw); } }
            cu=x2; cw=v2; }
        turn^=1; if(++steps>1000000) die("D no termination",N,u,v,w); }
      if(steps>maxD) maxD=steps;
      if(!goodD(cv,cw)){ exD++; ll o=(cv==1)?cw:cv; // (1,1,o) or (1,o,1), o ≡ 2 mod 3 or o=1
        if(o==1){ if(N!=5) die("D (1,1,1)",N,cu,cv,cw); }
        else if(o==5){ if(N!=29) die("D o=5",N,cu,cv,cw); }
        else { ll x2,v2; phi(1,o,&x2,&v2); if(!(v2%3==1&&v2>1)) die("D ex 1 step",N,cu,cv,cw); } } }
  }
  printf("n<%lld: C checked on %lld states (max walk %lld, %lld walks end at v=1 with a=1 or b=1); D on %lld states (max walk %lld, %lld end at u=1 with v=1 or w=1). OK\n",M,nC,maxC,exC,nD,maxD,exD); }

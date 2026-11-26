# End-to-end check of the proof's algorithm for three theorems.
#  F2: N=24n+7 = v^2+3a^2+3b^2  -> T+T+p5 (class 2) and T+T+P2 (class 1)
#  F1: N=24n+5 = 3u^2+v^2+w^2   -> T+p5+P2 (mixed)
# Steps: take the FIRST integer rep found that is not in the exceptional orbit (worst-case style seed),
# convert to all-odd by one omega-move, run the alternating descent, read off x,y,z, verify.
import sys, math
from math import gcd
T=lambda x:x*(x+1)//2; p5=lambda z:z*(3*z-1)//2; P2=lambda z:z*(3*z+1)//2
def omega_other(u,v):
    """(u,v) with 3u^2+v^2, u,v>0 odd: the other all-odd associate, and whether |v| class mod 3 flipped."""
    if (u-v)%4: return abs(u-v)//2,(v+3*u)//2,True
    if v>3*u: return (u+v)//2,(v-3*u)//2,True
    return (u+v)//2,(3*u-v)//2,False
def to_odd_pair(u,v):
    """(u,v) both even with u/2,v/2 of different parity -> an all-odd associate"""
    return abs(u-v)//2,(v+3*u)//2
def seeds_F2(N):
    for v in range(0,math.isqrt(N)+1):
        r=N-v*v
        if r%3: continue
        r//=3
        for a in range(0,math.isqrt(r)+1):
            b2=r-a*a; b=math.isqrt(b2)
            if b*b==b2: yield (v,a,b)
def seeds_F1(N):
    for u in range(0,math.isqrt(N//3)+1):
        r=N-3*u*u
        for v in range(0,math.isqrt(r)+1):
            w2=r-v*v; w=math.isqrt(w2)
            if w*w==w2: yield (u,v,w)
def cls(t): return t%3   # 1 or 2
def run_F2(n,target):
    N=24*n+7; steps=0
    for (v,a,b) in seeds_F2(N):
        g=gcd(gcd(v,a),b)
        if g*g*7==N and g>1: continue      # exceptional orbit of (k,k,k) when N=7k^2 (k>1): skip
        break
    else: raise Exception("no seed %d"%n)
    if v%2==0:                               # E-pattern: v even, exactly one of a,b even
        if a%2==0: a,v=to_odd_pair(a,v)
        else: b,v=to_odd_pair(b,v)
    assert v&1 and a&1 and b&1 and v*v+3*a*a+3*b*b==N
    turn=0
    while not (cls(v)==target or v==1):
        if turn==0: a,v,_=omega_other(a,v)
        else: b,v,_=omega_other(b,v)
        turn^=1; steps+=1
        assert steps<10**5
    x=(a-1)//2; y=(b-1)//2
    if target==2:
        z=(v+1)//6; assert T(x)+T(y)+p5(z)==n,(n,x,y,z)
    else:
        z=(v-1)//6; assert T(x)+T(y)+P2(z)==n,(n,x,y,z)
    return steps
def run_F1(n):
    N=24*n+5; steps=0
    for (u,v,w) in seeds_F1(N):
        g=gcd(gcd(u,v),w)
        if g*g*5==N and g>1: continue
        break
    else: raise Exception("no seed %d"%n)
    if u%2==0:
        if v%2==0: u,v=to_odd_pair(u,v)
        else: u,w=to_odd_pair(u,w)
    assert u&1 and v&1 and w&1 and 3*u*u+v*v+w*w==N
    turn=0
    while not (cls(v)!=cls(w) or v==1 or w==1):
        if turn==0: u,v,_=omega_other(u,v)
        else: u,w,_=omega_other(u,w)
        turn^=1; steps+=1
        assert steps<10**5
    if cls(v)==2 or (v==1 and cls(w)==1): v,w=w,v      # make v the class-1 one (second pentagonal), w the class-2 one
    x=(u-1)//2; y=(v-1)//6; z=(w+1)//6
    assert T(x)+P2(y)+p5(z)==n,(n,u,v,w)
    return steps
M=int(sys.argv[1]); mx=[0,0,0]
for n in range(M):
    mx[0]=max(mx[0],run_F2(n,2)); mx[1]=max(mx[1],run_F2(n,1) if n!=-1 else 0); mx[2]=max(mx[2],run_F1(n))
print("all n <",M,"verified for T+T+p5, T+T+P2, T+p5+P2; max descent steps:",mx)

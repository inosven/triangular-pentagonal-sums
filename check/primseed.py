# Sanity check of the classical input: primitive representations exist.
#  (C1) every N ≡ 5 (mod 24) is primitively represented by 3u^2+v^2+w^2
#  (C2) every N ≡ 7 (mod 24) is primitively represented by v^2+3a^2+3b^2
import math
from math import gcd
def prim1(N):
    for u in range(0,math.isqrt(N//3)+1):
        r=N-3*u*u
        for v in range(0,math.isqrt(r)+1):
            w2=r-v*v; w=math.isqrt(w2)
            if w*w==w2 and gcd(gcd(u,v),w)==1: return (u,v,w)
    return None
def prim2(N):
    for a in range(0,math.isqrt(N//3)+1):
        r=N-3*a*a
        for b in range(0,math.isqrt(r//3)+1):
            v2=r-3*b*b; v=math.isqrt(v2)
            if v*v==v2 and gcd(gcd(a,b),v)==1: return (v,a,b)
    return None
bad=[]
for n in range(0,60000):
    if prim1(24*n+5) is None: bad.append(('C1',24*n+5))
    if prim2(24*n+7) is None: bad.append(('C2',24*n+7))
print("all N<%d: failures:"%(24*60000),bad)
bad=[]
ks=[k for k in range(1,4000) if k%2 and k%3]
for k in ks:
    if prim1(5*k*k) is None: bad.append(('C1',k))
    if prim2(7*k*k) is None: bad.append(('C2',k))
print("N=5k^2 and 7k^2, k<4000 coprime to 6 (%d values): failures:"%len(ks),bad)

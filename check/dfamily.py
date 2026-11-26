# Finite checks for the size-constrained family, and comparison with Sun's list.
#   psi_{3,e}(x) + y(y+d)/2 + T(z),  e in {-1, 1, 5},  d odd.
# Theorem: universal over N  <=>  every n with 24n+c0+3(d^2-1) <= 87(d-2)^2 is represented  (c0 = 7 for e=±1, 31 for e=5).
import math, json
T=lambda z:z*(z+1)//2
def psi(a,b,x): return x*(a*x+b)//2
def representable(n,e,d):
    x=0
    while psi(3,e,x)<=n:
        r=n-psi(3,e,x); y=0
        while psi(1,d,y)<=r:
            t=r-psi(1,d,y); s=math.isqrt(8*t+1)
            if s*s==8*t+1: return True
            y+=1
        x+=1
    return False
sun=set(tuple(t) for t in json.load(open('sun_tuples_407.json')))
for e,c0 in ((-1,7),(1,7),(5,31)):
    for d in range(1,27,2):
        bound=(87*(d-2)**2-c0-3*(d*d-1))//24 if d>=3 else -1
        bad=[n for n in range(0,max(bound,0)+1) if not representable(n,e,d)]
        # also a longer sanity range
        bad2=[n for n in range(0,3000) if not representable(n,e,d)]
        inlist=(3,e,1,d,1,1) in sun
        print("(3,%d,1,%d,1,1): finite range n<=%d: %s | first failures in n<3000: %s | in Sun's list: %s"%(e,d,bound,"all represented" if not bad else "FAILS at %s"%bad[:5],bad2[:5],inlist))

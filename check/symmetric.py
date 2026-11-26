# The finite computation in the proof of Theorem 6.1 (for the tuple (3,-1,2,4,2,2)).
# s = (v,a,a), v ≡ 2 (mod 3), of type II (a ≡ v mod 4, v > 3a) or III- (a ≢ v mod 4, a < v);  x_1 = alpha(s);
# x_{i+1} = B x_i (i odd), A x_i (i even), 1 <= i < k <= 16, all entries positive; with (p,q) = (b_k,a_k) for odd k
# and (a_k,b_k) for even k, one of
#   E1      : v_k < 3p and (p+v_k)/2 = q      (the next triple, in case I, is symmetric)
#   E2-II   : v_k > 3p and (p+v_k)/2 = q      (the partner of (p,v_k), case II, gives a symmetric triple)
#   E2-III+ : p > v_k and (p-v_k)/2 = q       (case III)
#   E2-III- : p < v_k and (v_k-p)/2 = q       (case III)
# Each of the 2*16*4 cases is a linear equation for v/a. The program lists the solutions that satisfy all
# inequalities and, for each, runs the walk from the primitive triple (v,a,a).
from fractions import Fraction as Fr
def phi(u,v):
    if (u-v)%4==0:
        return ((u+v)//2,(3*u-v)//2) if v<3*u else ((u+v)//2,(v-3*u)//2)
    return (abs(u-v)//2,(3*u+v)//2)
def al(s): v,a,b=s; a2,v2=phi(a,v); return (v2,a2,b)
def be(s): v,a,b=s; b2,v2=phi(b,v); return (v2,a,b2)
def orbit(s0):
    s=s0; ph=0; orb=[s0]
    while True:
        s=al(s) if ph==0 else be(s); ph^=1
        if s==s0 and ph==0: return orb
        orb.append(s)
good=lambda t:(t[0]%3==2 or t[0]==1) and t[1]!=t[2]
class L:                      # linear forms p*lam + q in lam = v/a (with a = 1)
    def __init__(s,p,q): s.p=Fr(p); s.q=Fr(q)
    def __add__(s,o): return L(s.p+o.p,s.q+o.q)
    def __sub__(s,o): return L(s.p-o.p,s.q-o.q)
    def __rmul__(s,c): return L(c*s.p,c*s.q)
    def at(s,l): return s.p*l+s.q
h=Fr(1,2)
A=lambda s:(h*(3*s[1]-s[0]),h*(s[1]+s[0]),s[2])
B=lambda s:(h*(3*s[2]-s[0]),s[1],h*(s[2]+s[0]))
lam=L(1,0); one=L(0,1)
starts={'II':((h*(lam-3*one),h*(one+lam),one),lambda l:l>3),'III-':((h*(3*one+lam),h*(lam-one),one),lambda l:l>1)}
K=16; cases=0; positive=0; found=[]
for name,(x1,rng) in starts.items():
    run=[x1]
    for i in range(1,K): run.append(B(run[-1]) if i%2==1 else A(run[-1]))      # run[i-1] = x_i
    for k in range(1,K+1):
        v,a,b=run[k-1]; p,q=(b,a) if k%2==1 else (a,b)
        ends={'E1':(h*(p+v)-q,lambda vk,pk:vk<3*pk),'E2-II':(h*(p+v)-q,lambda vk,pk:vk>3*pk),
              'E2-III+':(h*(p-v)-q,lambda vk,pk:pk>vk),'E2-III-':(h*(v-p)-q,lambda vk,pk:pk<vk)}
        for en,(e,cond) in ends.items():
            cases+=1
            assert not (e.p==0 and e.q==0), "an equation holds identically"
            if e.p==0: continue
            l=-e.q/e.p
            if l<=0: continue
            positive+=1
            if rng(l) and all(x.at(l)>0 for st in run[:k] for x in st) and cond(v.at(l),p.at(l)): found.append((l,name,k,en))
print(cases,"cases;",positive,"have a solution v/a > 0;",len(found),"of these satisfy all inequalities:")
expected={Fr(5,3),Fr(39,17),Fr(17,7),Fr(3),Fr(27,7),Fr(5),Fr(7),Fr(23,3)}
assert {f[0] for f in found}==expected and len(found)==8
for l,name,k,en in sorted(found):
    v,a=l.numerator,l.denominator
    if v%2==1 and a%2==1 and v%3==2:
        orb=orbit((v,a,a)); g=[t for t in orb if good(t)]; assert g
        print("  v/a = %-5s (type %s, k=%d, %s): the walk from (%d,%d,%d) contains the good triple %s"%(l,name,k,en,v,a,a,g[0]))
    else:
        print("  v/a = %-5s (type %s, k=%d, %s): no primitive triple (v,a,a) with v, a odd and v ≡ 2 (mod 3)"%(l,name,k,en))
print("no case survives: the computation in the proof of Theorem 6.1 is confirmed")

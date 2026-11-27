# Check of Step 5 in the proof of Theorem 6.1 (the tuple (3,-1,2,4,2,2)): the formulas for x_1,...,x_5 and Table 1.
# s = (v,a,a) of type II:   x_1 = alpha(s) = ((v-3a)/2, (v+a)/2, a);
#             of type III-: x_1 = alpha(s) = ((v+3a)/2, (v-a)/2, a);
# x_2 = B x_1, x_3 = A x_2, x_4 = B x_3, x_5 = A x_4.  For x_k = (v_k,a_k,b_k) and (p,q) = (b_k,a_k) (k odd),
# (a_k,b_k) (k even) the three equations are (p+v_k)/2 = q, (p-v_k)/2 = q, (v_k-p)/2 = q.
from fractions import Fraction as Fr
import random
h=Fr(1,2)
A=lambda s:(h*(3*s[1]-s[0]),h*(s[1]+s[0]),s[2])
B=lambda s:(h*(3*s[2]-s[0]),s[1],h*(s[2]+s[0]))
def run(t,v,a):
    x=[((v-3*a)/2,(v+a)/2,a) if t=='II' else ((v+3*a)/2,(v-a)/2,a)]
    for i in range(1,5): x.append(B(x[-1]) if i%2==1 else A(x[-1]))
    return x
# 1. the formulas printed in the paper
for _ in range(500):
    v=Fr(random.randint(1,999),random.randint(1,99)); a=Fr(random.randint(1,999),random.randint(1,99))
    x=run('II',v,a)
    assert x[1]==((9*a-v)/4,(v+a)/2,(v-a)/4) and x[2]==((7*v-3*a)/8,(v+11*a)/8,(v-a)/4) and x[3][0]==-(v+3*a)/16
    y=run('III-',v,a)
    assert y[1]==((3*a-v)/4,(v-a)/2,(v+5*a)/4) and y[2]==((7*v-9*a)/8,(v+a)/8,(v+5*a)/4)
    assert y[3]==((39*a-v)/16,(v+a)/8,(9*v+a)/16) and y[4][0]==(7*v-33*a)/32
print("formulas for x_1,...,x_5: ok")
# 2. Table 1: each equation is c1*v + c2*a = 0; solutions as pairs (m,n) meaning m*v = n*a
table={('II',1):[(1,-3),(1,1),(1,-7)],('II',2):[(1,13),(1,5),(5,9)],('II',3):[(7,27),(1,-3),(3,23)],
       ('III-',1):[(1,7),(3,1),(1,3)],('III-',2):[(1,-9),(1,15),(1,-1)],('III-',3):[(7,1),(7,17),(1,7)],('III-',4):[(17,39),(5,-13),(3,5)]}
bold=[]
for (t,k),sols in table.items():
    for idx,(m,n) in enumerate(sols):
        # generic check that the equation is equivalent to m*v = n*a: evaluate the linear form at two points
        def form(v,a):
            vk,ak,bk=run(t,v,a)[k-1]; p,q=(bk,ak) if k%2==1 else (ak,bk)
            return [(p+vk)/2-q,(p-vk)/2-q,(vk-p)/2-q][idx]
        cv,ca=form(Fr(1),Fr(0)),form(Fr(0),Fr(1))
        assert cv!=0 and cv*n+ca*m==0, (t,k,idx)          # the solution set is the line m*v = n*a
        lam=Fr(n,m)
        ok = lam>0 and (lam>3 if t=='II' else lam>1) and (k<2 or (lam<9 if t=='II' else lam<3))
        if ok: bold.append((m,n,t,k))
print("Table 1: ok;",len(bold),"solutions are compatible with the inequalities:",", ".join("%dv=%da"%(m,n) for m,n,_,_ in bold))
assert sorted((m,n) for m,n,_,_ in bold)==sorted([(1,5),(7,27),(3,23),(1,7),(1,3),(7,17),(17,39),(3,5)])
# 3. the four triples and their good neighbours
def phi(u,v):
    if (u-v)%4==0:
        return ((u+v)//2,(3*u-v)//2) if v<3*u else ((u+v)//2,(v-3*u)//2)
    return (abs(u-v)//2,(3*u+v)//2)
def al(s): v,a,b=s; a2,v2=phi(a,v); return (v2,a2,b)
def be(s): v,a,b=s; b2,v2=phi(b,v); return (v2,a,b2)
assert al((5,1,1))==(1,3,1) and be(al((23,3,3)))==(1,13,5) and al((23,3,3))==(7,13,3)
assert al((17,7,7))==(19,5,7) and be((19,5,7))==(1,5,13) and al((5,3,3))==(7,1,3) and be((7,1,3))==(1,1,5)
print("the four remaining triples lead to good triples: ok")

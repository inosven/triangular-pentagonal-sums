# Not used in the paper. A bound from an earlier version of the proof of Theorem 6.1 ("nine points"),
# checked in exact rational arithmetic; the final proof replaces it by the explicit formulas for x_1,...,x_5.
# R = BA acts on triples (v,a,b); with pi(v,a,b) = (a-v, b-v) =: Y one has pi∘R = M1∘pi.
# For x = c*d + y, d = (1,1,1), y orthogonal to d:   tau(x) = 7c,
#   first entry of R^{-j} x = c - (3/7) S_j,  S_j = sum of the entries of M1^{-j} Y,
#   Q(x) = 7c^2 + (12 Y1^2 - 18 Y1 Y2 + 12 Y2^2)/7.
# Claim: if the first entries of R^{-j} x (0 <= j <= 8) are positive, then 2 tau(x)^2 > 11 Q(x).
# With c = 3/7 the hypothesis is S_j < 1; the region {S_j <= 1, 0<=j<=8} is a polygon and the convex
# function Q(y) is maximal at a vertex. The claim is equivalent to max Q(y) <= 27/77 (it is 2048/7581).
from fractions import Fraction as Fr
from itertools import combinations
from collections import Counter
Minv=[[Fr(-4,4),Fr(6,4)],[Fr(-6,4),Fr(5,4)]]
mul=lambda A,B:[[sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def polygon(J):
    P=[[Fr(1),Fr(0)],[Fr(0),Fr(1)]]; rows=[]
    for j in range(J+1):
        rows.append((P[0][0]+P[1][0],P[0][1]+P[1][1])); P=mul(Minv,P)
    verts=[]
    for i,j in combinations(range(J+1),2):
        (a,b),(c,d)=rows[i],rows[j]; det=a*d-b*c
        if det==0: continue
        Y=((d-b)/det,(a-c)/det)
        if all(r[0]*Y[0]+r[1]*Y[1]<=1 for r in rows): verts.append(Y)
    use=Counter(k for Y in verts for k,r in enumerate(rows) if r[0]*Y[0]+r[1]*Y[1]==1)
    closed=len(verts)>=3 and all(n==2 for n in use.values())   # every edge has two end points: bounded polygon
    return verts,closed
q=lambda Y:(12*Y[0]**2-18*Y[0]*Y[1]+12*Y[1]**2)/7
verts,closed=polygon(8)
m=max(q(Y) for Y in verts)
assert closed and len(verts)==9 and m==Fr(2048,7581) and m<Fr(27,77)
print("nine points: polygon with",len(verts),"vertices, max Q(y) =",m,"< 27/77: the lemma holds")
v7,c7=polygon(7)
assert max(q(Y) for Y in v7)>Fr(27,77)
print("eight points do not suffice (max Q(y) = %s > 27/77)"%max(q(Y) for Y in v7))

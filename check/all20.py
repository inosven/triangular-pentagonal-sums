# Brute-force sanity check of the 20 tuples (independent of the proofs), and membership in Sun's list.
import json, sys
sun=set(tuple(t) for t in json.load(open('sun_tuples_407.json')))
tuples=[(3,-1,1,d,1,1) for d in range(1,19,2)]+[(3,1,1,d,1,1) for d in (1,3,5,7)]+[(3,5,1,1,1,1),(3,5,1,3,1,1)]
tuples+=[(3,-1,2,2,2,0),(3,1,2,2,2,0),(3,5,2,2,2,0),(3,1,3,-1,1,1),(3,5,3,1,1,1)]
assert len(tuples)==20 and all(t in sun for t in tuples)
M=int(sys.argv[1])
psi=lambda a,b,x: x*(a*x+b)//2
for (a,b,c,d,e,f) in tuples:
    ok=bytearray(M)
    X=[]; x=0
    while psi(a,b,x)<M: X.append(psi(a,b,x)); x+=1
    Y=[]; y=0
    while psi(c,d,y)<M: Y.append(psi(c,d,y)); y+=1
    Z=[]; z=0
    while psi(e,f,z)<M: Z.append(psi(e,f,z)); z+=1
    YZ=bytearray(M)
    for p in Y:
        for q in Z:
            if p+q<M: YZ[p+q]=1
            else: break
    yz=[i for i in range(M) if YZ[i]]
    for p in X:
        for q in yz:
            if p+q<M: ok[p+q]=1
            else: break
    assert all(ok),((a,b,c,d,e,f),ok.index(0))
print("all 20 tuples are in Sun's list and represent every n <",M)
# refinements: n>=1 => z>=1 in Theorem 1.1 ; y>=1 in Theorem 1.4
T=lambda x:x*(x+1)//2; p5=lambda x:x*(3*x-1)//2; P5=lambda x:x*(3*x+1)//2
M2=min(M,20000)
TT=bytearray(M2)
ts=[T(x) for x in range(300) if T(x)<M2]
for p in ts:
    for q in ts:
        if p+q<M2: TT[p+q]=1
for n in range(1,M2):
    z=1; found=False
    while p5(z)<=n:
        if TT[n-p5(z)]: found=True; break
        z+=1
    assert found,n
    found=False; y=1
    while p5(y)<=n and not found:
        r=n-p5(y); z=0
        while P5(z)<=r:
            t=r-P5(z); s=int((8*t+1)**0.5)
            while s*s>8*t+1: s-=1
            while (s+1)*(s+1)<=8*t+1: s+=1
            if s*s==8*t+1: found=True; break
            z+=1
        y+=1
    assert found,n
print("refinements (z>=1, resp. y>=1, for n>=1) hold for n <",M2)

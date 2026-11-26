# The only computation used in the proof of Theorem 1.2:
# for (e,d) with d >= 3 in the universal range, every n with 24n+e^2+3d^2+3 <= 87(d-2)^2
# is psi_{3,e}(x) + psi_{1,d}(y) + T(z) with x,y,z >= 0.  Writes a certificate and re-verifies it.
import math, json
psi=lambda a,b,x: x*(a*x+b)//2
def find(n,e,d):
    x=0
    while psi(3,e,x)<=n:
        r=n-psi(3,e,x); y=0
        while psi(1,d,y)<=r:
            t=r-psi(1,d,y); s=math.isqrt(8*t+1)
            if s*s==8*t+1: return (x,y,(s-1)//2)
            y+=1
        x+=1
    return None
pairs=[(-1,d) for d in range(3,19,2)]+[(1,d) for d in (3,5,7)]+[(5,3)]
cert={}; total=0; worst=0
for e,d in pairs:
    bound=(87*(d-2)**2-e*e-3*d*d-3)//24
    worst=max(worst,bound)
    rows=[]
    for n in range(bound+1):
        r=find(n,e,d); assert r is not None,(e,d,n)
        rows.append([n,*r])
    cert["%d,%d"%(e,d)]=rows; total+=len(rows)
json.dump(cert,open('finite_range_certificate.json','w'))
# independent re-verification of the certificate
cert=json.load(open('finite_range_certificate.json'))
for key,rows in cert.items():
    e,d=map(int,key.split(','))
    bound=(87*(d-2)**2-e*e-3*d*d-3)//24
    assert [r[0] for r in rows]==list(range(bound+1))
    for n,x,y,z in rows:
        assert x>=0 and y>=0 and z>=0 and psi(3,e,x)+psi(1,d,y)+psi(1,1,z)==n
print("pairs:",len(pairs),"cases:",total,"largest n:",worst,"-> certificate verified")

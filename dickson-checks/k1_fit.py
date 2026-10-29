# For k = 1 the true coefficient of P^R on wt_n is computable in closed form.
# This searches a family of candidate formulas and shows that
# (-1)^d(R) * (code's coefficient), i.e. the formula for wt_n, fits all cases.
# Table 1, row 1.  Plain Python 3, no Sage needed.
#
# Run:  python3 dickson-checks/k1_fit.py
import itertools
from math import comb
def binp(p,a,b):
    if b<0: return 0
    if a>=0: return comb(a,b)%p
    return ((-1)**b*comb(-a+b-1,b))%p
def multinom(p,parts):
    s=0;c=1
    for a in parts:
        s+=a;c=c*binp(p,s,a)%p
    return c
def gam(p,m): return binp(p,-(p-1)*m,m)
data=[]
for p in [3,5,7]:
    for n in range(0,60):
        for J in [1,2]:
            for Rv in itertools.product(range(0,8 if J==1 else 4),repeat=J):
                if not any(Rv): continue
                d=sum(r*(p**(j+1)-1)//(p-1) for j,r in enumerate(Rv))
                g2=gam(p,n+d)
                if g2==0: continue
                m=(p-1)*n
                truth=gam(p,n)*binp(p,m,sum(Rv))*multinom(p,Rv)*pow(g2,p-2,p)%p
                data.append((p,n,Rv,d,truth))
print(len(data),"data points")
best=[]
rng=range(-2,3)
for al,be,ga,de in itertools.product(rng,repeat=4):
  for sg in ['1','R','N','d','n']:
    for mt in ['pR','R']:
        ok=0
        for (p,n,Rv,d,truth) in data:
            N=sum(r*p**(j+1) for j,r in enumerate(Rv)); R=sum(Rv)
            X=al*(p-1)*n+be*R+ga*N+de*(p-1)*d
            parts=[r*p**(j+1) for j,r in enumerate(Rv)] if mt=='pR' else list(Rv)
            M=sum(parts)
            s={'1':1,'R':(-1)**R,'N':(-1)**N,'d':(-1)**d,'n':(-1)**n}[sg]
            c=s*multinom(p,parts)*binp(p,X,M)%p
            if c==truth: ok+=1
        best.append((ok,al,be,ga,de,sg,mt))
best.sort(reverse=True)
for b in best[:8]: print(b)

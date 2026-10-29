# Checks the binomial identity (antipode identity) of Proposition 5.12, eq. (8):
#   sum_{R'+R''=R} b(R', n+d(R'')) a(R'', n) = 0   for R != 0,
# which implies the conjugate formula (Conjecture 4.6).  Plain Python 3.
#
# Run:  python3 dickson-checks/antipode.py
import itertools
from math import comb
def binp(p,a,b):
    if b<0: return 0
    if a<0:  # binom(a,b) = (-1)^b binom(b-a-1,b)
        return ((-1)**b*binp(p,b-a-1,b))%p
    if b>a: return 0
    r=1
    while a or b:
        r=r*comb(a%p,b%p)%p; a//=p; b//=p
    return r
def multi(p,parts):
    s=0;c=1
    for x in parts: s+=x; c=c*binp(p,s,x)%p
    return c
def N(p,R): return sum(r*p**(j+1) for j,r in enumerate(R))
def d(p,R): return sum(r*(p**(j+1)-1)//(p-1) for j,r in enumerate(R))
def a(p,R,n): return binp(p,(p-1)*(n+d(p,R)),N(p,R))*multi(p,[r*p**(j+1) for j,r in enumerate(R)])%p
def b(p,R,n): return binp(p,-(p-1)*n,N(p,R))*multi(p,[r*p**(j+1) for j,r in enumerate(R)])%p
bad=0; tot=0
for p in [2,3,5]:
  for J in ([1,2,3] if p<5 else [1,2]):
    for R in itertools.product(range(0,p+2),repeat=J):
      if not any(R): continue
      for n in range(0,25):
        s=0
        for R2 in itertools.product(*[range(r+1) for r in R]):
          R1=tuple(r-x for r,x in zip(R,R2))
          s+=b(p,R1,n+d(p,R2))*a(p,R2,n)
        tot+=1
        if s%p: 
          bad+=1
          if bad<5: print("fail",p,R,n,s%p)
print("antipode identity: tested",tot,"failures",bad)

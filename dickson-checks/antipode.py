# Checks the binomial identity (antipode identity) of Proposition 5.12, eq. (8):
#   sum_{R'+R''=R} b(R', n+d(R'')) a(R'', n) = 0   for R != 0,
# which gives the conjugate formula (Theorem 4.6), and the more general
# Lemma 5.13 used to prove it.  Plain Python 3.
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

# Lemma 5.13: [y^E] Pi_lam(Y^mu) Pi_lam(Y^nu) = 0 if mu + nu = |E| - delta,
# 1 <= delta <= sum_i E_i / p^lam_i.
def coefY(p,m,A):
    s=sum(A); v=binp(p,m,s); t=0
    for x in A: t+=x; v=v*binp(p,t,x)%p
    return v
def G(p,lam,mu,nu,E):
    # [y^E] Pi_lam(Y^mu) Pi_lam(Y^nu): sum over splits A+B=E with p^lam_i | A_i, B_i
    tot=0
    for A in itertools.product(*[range(0,e+1,p**l) for e,l in zip(E,lam)]):
        B=[e-a for e,a in zip(E,A)]
        if any(b % p**l for b,l in zip(B,lam)): continue
        tot+=coefY(p,mu,A)*coefY(p,nu,B)
    return tot%p
bad=0; tot=0
for p in [2,3]:
  for J in [1,2,3]:
    for lam in itertools.product(range(0,3),repeat=J):
      for cnt in itertools.product(range(0,3),repeat=J):
        E=[c*p**l for c,l in zip(cnt,lam)]
        if not any(E): continue
        count=sum(cnt)
        for delta in range(1,count+1):
          for mu in range(-25,26):
            nu=sum(E)-delta-mu; tot+=1
            if G(p,lam,mu,nu,E):
              bad+=1
              if bad<5: print("FAIL",p,lam,E,delta,mu)
print("general level lemma: tested",tot,"failures",bad)

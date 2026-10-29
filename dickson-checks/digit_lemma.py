# Brute-force check of the vanishing statement in Proposition 5.8 (at D0 = p^k, i.e. Theorem 5.9):
# G_{R,E} = 0 whenever the base-p digit sum of D_R - E is <= (k-1)(p-1).
# Table 1, last row.  Plain Python 3, no Sage needed.
#
# Run:  python3 dickson-checks/digit_lemma.py
import itertools, random
from math import comb, factorial
def binp(p,a,b):
    if b<0 or a<0 or b>a: return 0
    r=1
    while a or b:
        r=r*comb(a%p,b%p)%p; a//=p; b//=p
    return r
def coef(p,c,B):   # [y^B](1+sum y)^c, c>=0
    s=sum(B)
    if s>c: return 0
    v=binp(p,c,s); t=0
    for b in B:
        t+=b; v=v*binp(p,t,b)%p
    return v
def ds(p,n):
    s=0
    while n: s+=n%p; n//=p
    return s
def gt(p,a):  # coefficient of z^{(p-1)a} in 1-S(z)^{p-1}
    E=(p-1)*a
    if a==0: return 1
    if ds(p,E)!=p-1: return 0
    digs=[];x=E
    while x: digs.append(x%p); x//=p
    v=1
    for d in digs: v=v*factorial(d)%p
    return pow(v,p-2,p)
viol=0; tested=0
for p in [2,3,5]:
  for k in [1,2,3,4]:
    for J in [1,2,3]:
      for R in itertools.product(range(0,p+2),repeat=J):
        N=sum(r*p**(j+1) for j,r in enumerate(R)); d=sum(r*(p**(j+1)-1)//(p-1) for j,r in enumerate(R))
        D=p**k+(p-1)*d
        pR=[r*p**(j+1) for j,r in enumerate(R)]
        binf=coef(p,D,pR)
        delta={}
        e=0
        while p**e<=D:
            s=0
            for j in range(e+1,J+1):
                if R[j-1]>=1:
                    B=list(pR); B[j-1]-=p**e
                    s+=coef(p,D-p**e,B)
            delta[e]=s%p; e+=1
        for E in range(1,D+1):
            G=(binf if E==1 else 0)
            for e,de in delta.items():
                if de and E>=p**e and (E-p**e)%(p-1)==0: G-=de*gt(p,(E-p**e)//(p-1))
            G%=p; tested+=1
            if G and ds(p,D-E)<=(k-1)*(p-1):
                viol+=1
                if viol<5: print("VIOLATION",p,k,R,E)
print("tested",tested,"violations",viol)

# General degrees D0 (Proposition 5.8): the same vanishing for every D0 with
# alpha(D0 - 1) > (k-1)(p-1), where D_R = D0 + (p-1) d(R).
viol=0; tested=0
for p in [2,3,5]:
  for k in [1,2,3]:
    for J in [1,2]:
      for R in itertools.product(range(0,p+2),repeat=J):
        N=sum(r*p**(j+1) for j,r in enumerate(R)); d=sum(r*(p**(j+1)-1)//(p-1) for j,r in enumerate(R))
        pR=[r*p**(j+1) for j,r in enumerate(R)]
        for D0 in range(1,p**(k+1)+p):
          if (D0-1)%(p-1) or ds(p,D0-1) <= (k-1)*(p-1): continue
          D=D0+(p-1)*d
          binf=coef(p,D,pR); delta={}; e=0
          while p**e<=D:
            s=0
            for j in range(e+1,J+1):
              if R[j-1]>=1:
                B=list(pR); B[j-1]-=p**e; s+=coef(p,D-p**e,B)
            delta[e]=s%p; e+=1
          for E in range(1,D+1):
            G=(binf if E==1 else 0)
            for e,de in delta.items():
              if de and E>=p**e and (E-p**e)%(p-1)==0: G-=de*gt(p,(E-p**e)//(p-1))
            G%=p; tested+=1
            if G and ds(p,D-E)<=(k-1)*(p-1):
              viol+=1
              if viol<5: print("VIOLATION",p,k,R,D0,E)
print("general D0: tested",tested,"violations",viol)

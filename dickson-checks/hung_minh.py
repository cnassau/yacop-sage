# Compares yacop's action of single powers P^i (Sq^i for p=2) on the Dickson
# invariants Q_{k,s} = (-1)^(k-s) c_{k,s} with the formulas of Hung (p=2,
# PAMS 1991) and Hung-Minh (odd p, Vietnam J. Math. 1995; restated in Sum,
# arXiv:2111.07073, Thm 3.4).  See the remark after Corollary 5.10.
#
# Run:  ./yacop.sh -c "$(cat dickson-checks/hung_minh.py)"
import yacop, sys
from yacop.modules.dickson import DicksonAlgebra
def digits(p, r, n): return [(r // p**i) % p for i in range(n)]
def HM(p, n, s, r, Q):
    # Hung-Minh: P^r Q_{n,s}, Q = list Q[i] for i=0..n (Q[n]=1)
    if r == p**n - p**s: return Q[s]**p
    if r > p**n - p**s: return 0
    a = digits(p, r, n); am = lambda i: a[i] if i >= 0 else 0
    for i in range(n):
        if i != s and a[i] < am(i-1): return 0
    if a[s] + 1 < am(s-1): return 0
    c = Integer((-1)**a[n-1]) * factorial(a[n-1]) * (a[s]+1)
    den = factorial(a[s]+1-am(s-1)) * prod(factorial(a[i]-am(i-1)) for i in range(n) if i != s)
    c = GF(p)(c) / GF(p)(den)
    # exponent of Q_i is alpha_i - alpha_{i-1}, plus 1 for i = s
    return c * prod(Q[i]**(a[i] - am(i-1) + (1 if i == s else 0)) for i in range(n))
def Hung(n, s, i, Q):
    # p=2: Sq^i Q_{n,s}
    if i == 2**n - 2**s: return Q[s]**2
    for r in range(0, s+1):
        if i == 2**s - 2**r: return Q[r]
    for r in range(0, s+1):
        for t in range(s+1, n+1):
            if i == 2**n - 2**t + 2**s - 2**r: return Q[r]*Q[t]
    return 0
def run(p, k):
    D = DicksonAlgebra(p, k)
    ds = [g for g in D.gens() if g.e == 0] if p > 2 else list(D.gens())
    # ds[j-1] = c_{k,k-j}
    c = {k-j: ds[j-1] for j in range(1, k+1)}; c[k] = D.one()
    Q = [(-1)**(k-i) * c[i] for i in range(k+1)]
    A = SteenrodAlgebra(p) if p > 2 else SteenrodAlgebra(2)
    good = bad = 0
    for s in range(k):
        for r in range(0, p**k - p**s + 1):
            lhs = (A.P(r) if p > 2 else Sq(r)) * Q[s]
            rhs = HM(p, k, s, r, Q) if p > 2 else Hung(k, s, r, Q)
            if lhs == rhs: good += 1
            else:
                bad += 1
                if bad < 5: print("   mismatch p=%d k=%d s=%d r=%d: code %s, literature %s" % (p,k,s,r,lhs,rhs))
    print("p=%d k=%d: %d agree, %d disagree" % (p,k,good,bad)); sys.stdout.flush()
run(2,3); run(2,4); run(3,2); run(3,3); run(5,2); run(7,2)

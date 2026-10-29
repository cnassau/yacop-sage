# Checks P^R Omega_n = a(R,n) Omega_{n+d(R)} for the Lagrange-defined Peterson
# elements Omega_n in the perfect closure of D_k, for all n (including degrees
# where Omega_n is not a polynomial).  Fractional exponents are cleared by
# raising to the p^K-th power: (P^R y)^(p^K) = P^(p^K R)(y^(p^K)).  Table 1, row 5.
#
# Run:  ./yacop.sh -c "$(cat dickson-checks/lagrange_action.py)"
from sage.all import *
import itertools, sys
def binp(p, a, b):
    if b < 0: return GF(p)(0)
    return GF(p)(binomial(a, b))
def multinom(p, parts):
    s = 0; c = GF(p)(1)
    for a in parts:
        s += a; c *= binp(p, s, a)
    return c
def dickson(p, k, R, xs):
    T = PolynomialRing(R, 'X'); X = T.gen()
    f = prod(X - sum(a*x for a, x in zip(v, xs)) for v in itertools.product(range(p), repeat=k))
    return [R(f[p**i]) for i in range(k+1)]   # c_0..c_k, f = sum c_i X^(p^i)
def Omega_pow(p, k, n, c, K):
    # (Omega_n)^(p^K) where Omega_n = sum_R binom(-m,|R|) multinom(R) prod_j q_j^{r_j}, q_j^(p^(k-j)) = c_{k-j}
    m = (p-1)*n; ans = 0
    def rec(j, rem):
        if j > k:
            if rem == 0: yield []
            return
        for r in range(rem//(p**j-1)+1):
            for rest in rec(j+1, rem-r*(p**j-1)): yield [r]+rest
    for Rv in rec(1, m):
        cf = multinom(p, Rv)*binp(p, -m, sum(Rv))
        if cf == 0: continue
        term = cf
        for j in range(1, k+1):
            e = Rv[j-1]*p**K
            assert e % p**(k-j) == 0
            term *= c[k-j]**(e//p**(k-j))
        ans += term
    return ans
def run(p, k, nmax, J, rmax, K):
    names = ['x%d'%(i+1) for i in range(k)] + ['t%d'%(j+1) for j in range(J)]
    R = PolynomialRing(GF(p), names); xs = R.gens()[:k]; ts = R.gens()[k:]
    c = dickson(p, k, R, xs)
    sub = {x: x + sum(t*x**(p**(j+1)) for j, t in enumerate(ts)) for x in xs}
    good = bad = 0
    for n in range(nmax+1):
        W = Omega_pow(p, k, n, c, K)
        if W == 0: continue
        WW = W.subs(sub)
        for Rv in itertools.product(range(rmax+1), repeat=J):
            if not any(Rv): continue
            d = sum(r*(p**(j+1)-1)//(p-1) for j, r in enumerate(Rv))
            lhs = WW.coefficient({t: r*p**K for t, r in zip(ts, Rv)}).subs({t: 0 for t in ts})
            N = sum(r*p**(j+1) for j, r in enumerate(Rv))
            a = multinom(p, [r*p**(j+1) for j, r in enumerate(Rv)])*binp(p, (p-1)*(n+d), N)
            if lhs == a*Omega_pow(p, k, n+d, c, K): good += 1
            else:
                bad += 1
                if bad < 4: print("   mismatch n=%d R=%s" % (n, Rv))
    print("Lagrange Omega, all n: p=%d k=%d nmax=%d K=%d: good=%d bad=%d" % (p,k,nmax,K,good,bad)); sys.stdout.flush()
run(2, 2, 12, 2, 2, 1)
run(2, 3, 9, 1, 3, 2)
run(3, 2, 7, 1, 2, 1)

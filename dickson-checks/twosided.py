# Two-sided Peterson elements Theta_n (dickson.tex, Section 5.5), all p.
#   Theta(w) = prod_i (1 - S^(x_i w)^(p-1)),  S^(z) = sum_{r in Z} z^(p^r).
# Checks
#  - Theorem 5.18: Omega_n = Theta_n, compared after raising to the p^K-th
#    power (digits below position -K are dropped; repeating with K+1 shows
#    this does not matter);
#  - Lemma 5.16(2): Theta_n has integral exponents  <=>  sigma_p(n) >= k;
#  - Lemma 5.19: the x_1-degree-0 part of tau(wt_n) - wt_n, tau: x_1 -> x_1+x_2;
#  - Corollary 5.20: wt_n is tau-invariant  <=>  sigma_p(n) >= k.
#
# Run:  ./yacop.sh -c "$(cat dickson-checks/twosided.py)"
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
    return [R(f[p**i]) for i in range(k+1)]
def Omega_pow(p, k, n, c, K):
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
            term *= c[k-j]**(e//p**(k-j))
        ans += term
    return ans
def admissible(p, M):
    # integers 0 < a <= M with base-p digit sum p-1, with coefficient 1/eps!
    out = [(0, GF(p)(1))]
    L = 0
    while p**L <= M: L += 1
    def rec(pos, left, val, cf):
        if left == 0:
            if 0 < val <= M: out.append((val, cf))
            return
        if pos >= L: return
        for e in range(left+1):
            rec(pos+1, left-e, val+e*p**pos, cf/GF(p)(factorial(e)))
    rec(0, p-1, 0, GF(p)(1))
    return out
def twosided_pow(p, xs, M):
    # (coefficient of w^M in prod_i (1 - T_p(x_i w)^(p-1)))^(p^K), with exponents scaled by p^K (=M/((p-1)n))
    adm = admissible(p, M); ans = 0
    def rec(i, rem, mono):
        nonlocal ans
        if i == len(xs):
            if rem == 0: ans += mono
            return
        for a, cf in adm:
            if a <= rem: rec(i+1, rem-a, mono*cf*xs[i]**a)
    rec(0, M, xs[0].parent()(1))
    return ans
def run(p, k, nmax, K):
    R = PolynomialRing(GF(p), ['x%d'%(i+1) for i in range(k)]); xs = R.gens()
    c = dickson(p, k, R, xs)
    good = bad = 0; badlist = []
    for n in range(nmax+1):
        O = Omega_pow(p, k, n, c, K)
        Tn = twosided_pow(p, xs, (p-1)*n*p**K)
        if O == Tn: good += 1
        else:
            bad += 1; badlist.append(n)
    print("Omega_n = Theta_n: p=%d k=%d n<=%d K=%d: good=%d bad=%d %s" % (p, k, nmax, K, good, bad, badlist[:8])); sys.stdout.flush()
def sigma(p, n):
    m = (p-1)*n; a = sum(ZZ(m).digits(p)); v = ZZ(n).valuation(p)
    return a//(p-1) + v
def S_pow_coeffs(p, e, M):
    # coefficients of S(z)^e (one-sided), exponents <= M: dict exponent -> coeff
    res = {}
    L = 0
    while p**L <= M: L += 1
    def rec(pos, left, val, cf):
        if left == 0:
            if val <= M: res[val] = res.get(val, 0) + cf
            return
        if pos >= L: return
        for d in range(left+1):
            rec(pos+1, left-d, val+d*p**pos, cf/GF(p)(factorial(d)))
    rec(0, e, 0, GF(p)(factorial(e)))
    return res
def run_crit(p, k, nmax):
    R = PolynomialRing(GF(p), ['x%d'%(i+1) for i in range(k)]); xs = R.gens()
    bad = 0
    for n in range(1, nmax+1):
        m = (p-1)*n
        wt = twosided_pow(p, xs, m)                     # integral part = wt_n
        Th = twosided_pow(p, xs, m*p**k)                # Theta_n^(p^k)
        integral = (Th == wt**(p**k))
        tw = wt.subs({xs[0]: xs[0]+xs[1]})
        invariant = (tw == wt)
        # x_1-degree-0 part of tau(wt)-wt  vs  -x2 S(x2)^(p-2) * prod_{l>=3} G(x_l), degree m
        diff = (tw - wt).subs({xs[0]: 0})
        pred = 0
        for e, cf in S_pow_coeffs(p, p-2, m-1).items():
            rest = twosided_pow(p, xs[2:], m-1-e) if k > 2 else (1 if m-1-e == 0 else 0)
            pred += -cf * xs[1]**(e+1) * rest
        s = sigma(p, n)
        ok = integral == (s >= k) and invariant == (s >= k) and diff == pred
        if not ok:
            bad += 1; print("  fail n=%d sigma=%d integral=%s invariant=%s transv=%s" % (n, s, integral, invariant, diff == pred))
    print("criterion p=%d k=%d n<=%d: bad=%d" % (p, k, nmax, bad)); sys.stdout.flush()
for args in [(3,1,20,2), (3,2,30,3), (3,3,12,4), (5,1,12,2), (5,2,16,3), (5,3,3,3), (7,2,10,3),
             (3,2,14,4), (5,2,8,4), (3,3,6,5)]:
    run(*args)
for args in [(2,3,40), (3,2,45), (3,3,30), (5,2,30), (5,3,12), (7,2,20)]:
    run_crit(*args)

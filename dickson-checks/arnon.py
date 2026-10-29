# Compares the Lagrange elements Omega_n (p = 2) with Arnon's generalized
# Peterson elements  k_omega_n = sum of x_1^{s_1}...x_k^{s_k} over s_1+...+s_k = n,
# each s_i zero or a power of 2 (negative powers allowed), see
# D. Arnon, Generalized Dickson invariants, Israel J. Math. 118 (2000), Def. 3.2.
# Arnon has k_omega_{2n} = k_omega_n^2, and k_omega_M only involves integral
# exponents when alpha(M) + nu(M) >= k (his Prop. 3.4).  So we compare
#   Omega_n^(2^K)  with  k_omega_{2^K n}  (computed with integral exponents),
# with K = k, which makes both sides honest polynomials.
#
# It also checks the transvection identity
#   omega_n(x_1+x_2, x_2, ..., x_k) = omega_n + x_2 * omega_{n-1}(x_3, ..., x_k)
# for the integral Peterson elements omega_n, and the resulting criterion
#   omega_n is GL_k-invariant  <=>  alpha(n) + nu(n) >= k.
#
# Run:  ./yacop.sh -c "$(cat dickson-checks/arnon.py)"
from sage.all import *
import itertools, sys
def dickson(k, R, xs):
    T = PolynomialRing(R, 'X'); X = T.gen()
    f = prod(X - sum(a*x for a, x in zip(v, xs)) for v in itertools.product(range(2), repeat=k))
    return [R(f[2**i]) for i in range(k+1)]   # c_0..c_k, f = sum c_i X^(2^i)
def Omega_pow(k, n, c, K):
    # (Omega_n)^(2^K), Omega_n = sum_R binom(-n,|R|) multinom(R) prod_j q_j^{r_j}, q_j^(2^(k-j)) = c_{k-j}
    ans = 0
    def rec(j, rem):
        if j > k:
            if rem == 0: yield []
            return
        for r in range(rem//(2**j-1)+1):
            for rest in rec(j+1, rem-r*(2**j-1)): yield [r]+rest
    for Rv in rec(1, n):
        s = 0; cf = GF(2)(1)
        for r in Rv:
            s += r; cf *= binomial(s, r)
        cf *= binomial(-n, s)
        if cf == 0: continue
        term = cf
        for j in range(1, k+1):
            e = Rv[j-1]*2**K
            term *= c[k-j]**(e//2**(k-j))
        ans += term
    return ans
def arnon_omega(M, xs):
    # integral-exponent part of Arnon's k_omega_M; exact when alpha(M)+nu(M) >= k
    pw = [0] + [2**r for r in range(int(M).bit_length())]
    ans = 0
    for s in itertools.product(pw, repeat=len(xs)):
        if sum(s) == M: ans += prod(x**e for x, e in zip(xs, s))
    return ans
def run(k, nmax):
    R = PolynomialRing(GF(2), ['x%d'%(i+1) for i in range(k)]); xs = R.gens()
    c = dickson(k, R, xs); K = k
    good = bad = 0
    for n in range(nmax+1):
        if Omega_pow(k, n, c, K) == arnon_omega(2**K*n, xs): good += 1
        else:
            bad += 1; print("   differ at n=%d" % n)
    print("Arnon k_omega_n = Omega_n: k=%d n<=%d: good=%d bad=%d" % (k, nmax, good, bad)); sys.stdout.flush()
def sigma(n):
    return bin(n).count('1') + (n & -n).bit_length() - 1
def run_invariance(k, nmax):
    R = PolynomialRing(GF(2), ['x%d'%(i+1) for i in range(k)]); xs = R.gens()
    good = bad = 0
    for n in range(1, nmax+1):
        w = arnon_omega(n, xs)       # = integral omega_n (all exponents >= 0)
        Tw = w.subs({xs[0]: xs[0]+xs[1]})
        rest = arnon_omega(n-1, xs[2:]) if k > 2 else R(1 if n == 1 else 0)
        ok = (Tw - w == xs[1]*rest) and ((Tw == w) == (sigma(n) >= k))
        if ok: good += 1
        else:
            bad += 1; print("   transvection/criterion fails at n=%d" % n)
    print("transvection identity and criterion: k=%d n<=%d: good=%d bad=%d" % (k, nmax, good, bad)); sys.stdout.flush()
run_invariance(2, 40)
run_invariance(3, 40)
run_invariance(4, 40)
run(1, 30)
run(2, 40)
run(3, 24)
run(4, 10)

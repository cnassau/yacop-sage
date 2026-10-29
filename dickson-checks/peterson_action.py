# Checks the action formula (*) and its conjugate version on the GL_k-invariant
# Peterson elements wt_n = (-1)^n omega_n, and the decomposition of wt_n into
# Dickson monomials (Conjecture 4.4 / Lagrange formula).  The action is computed
# directly on polynomials by x_i -> x_i + sum_j t_j x_i^(p^j) (or its
# compositional inverse for chi), independently of yacop.  Table 1, rows 2-4.
#
# Run:  ./yacop.sh -c "$(cat dickson-checks/peterson_action.py)"
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
def omegat(p, k, n, R, xs):
    # tilde omega_n = (-1)^n omega_n
    gam = lambda m: binp(p, -(p-1)*m, m)
    ans = R(0)
    for e in IntegerVectors(n, k):
        c = prod(gam(a) for a in e)
        if c: ans += c*prod(x**((p-1)*a) for x, a in zip(xs, e))
    return (-1)**n*ans
def isinv(w, xs):
    return len(xs) == 1 or w.subs({xs[0]: xs[0]+xs[1]}) == w
def run(p, k, nmax, J, rmax, conj):
    names = ['x%d'%(i+1) for i in range(k)] + ['t%d'%(j+1) for j in range(J)]
    R = PolynomialRing(GF(p), names); xs = R.gens()[:k]; ts = R.gens()[k:]
    JC = rmax*J*(J+1)//2 if conj else J
    tt = list(ts) + [R(0)]*JC
    c = [R(1)]
    for nn in range(1, JC+1):
        c.append(-sum(tt[nn-i-1]**(p**i)*c[i] for i in range(nn)) if conj else tt[nn-1])
    sub = {x: sum(c[j]*x**(p**j) for j in range(JC+1)) for x in xs}
    good = bad = 0
    for n in range(nmax+1):
        w = omegat(p, k, n, R, xs)
        if w == 0 or not isinv(w, xs): continue
        W = w.subs(sub)
        for Rv in itertools.product(range(rmax+1), repeat=J):
            if not any(Rv): continue
            d = sum(r*(p**(j+1)-1)//(p-1) for j, r in enumerate(Rv))
            lhs = W.coefficient({t: r for t, r in zip(ts, Rv)}).subs({t: 0 for t in ts})
            N = sum(r*p**(j+1) for j, r in enumerate(Rv))
            m = multinom(p, [r*p**(j+1) for j, r in enumerate(Rv)])
            cf = m*(binp(p, -(p-1)*n, N) if conj else binp(p, (p-1)*(n+d), N))
            if lhs == cf*omegat(p, k, n+d, R, xs): good += 1
            else:
                bad += 1
                if bad < 4: print("   MISMATCH n=%d R=%s" % (n, Rv))
    print("action p=%d k=%d nmax=%d J=%d rmax=%d conj=%s: good=%d bad=%d" % (p,k,nmax,J,rmax,conj,good,bad)); sys.stdout.flush()

def decomp(p, k, nmax):
    # check: tilde omega_n = sum_R multinom(R) binom(-(p-1)n,|R|) prod_j omt(gen_j)^(r_j/p^(k-j))
    R = PolynomialRing(GF(p), ['x%d'%(i+1) for i in range(k)]); xs = R.gens()
    gens = {}
    for j in range(1, k+1):
        # generator with Milnor index j: Q_{k,k-j}, Peterson index n_j = p^(k-j)(p^j-1)/(p-1)
        gens[j] = omegat(p, k, p**(k-j)*(p**j-1)//(p-1), R, xs)
    good = bad = notinv = 0
    for n in range(nmax+1):
        w = omegat(p, k, n, R, xs)
        if not isinv(w, xs): notinv += 1; continue
        tot = R(0); ok = True
        m = (p-1)*n
        # enumerate R with sum r_j (p^j-1) = m
        def rec(j, rem):
            if j > k:
                if rem == 0: yield []
                return
            w_ = p**j-1
            for r in range(rem//w_+1):
                for rest in rec(j+1, rem-r*w_): yield [r]+rest
        for Rv in rec(1, m):
            cf = multinom(p, Rv)*binp(p, -m, sum(Rv))
            if cf == 0: continue
            if any(Rv[j-1] % p**(k-j) for j in range(1, k+1)): ok = False; continue
            tot += cf*prod(gens[j]**(Rv[j-1]//p**(k-j)) for j in range(1, k+1))
        if ok and tot == w: good += 1
        else: bad += 1; print("   decomp mismatch n=%d ok=%s" % (n, ok))
    print("decomp p=%d k=%d nmax=%d: good=%d bad=%d noninvariant=%d" % (p,k,nmax,good,bad,notinv)); sys.stdout.flush()

# ordinary action
for (p, k, nmax, J, rmax) in [(2,2,16,2,4), (2,3,14,2,3), (3,1,30,2,3), (3,2,14,2,2),
                              (3,3,14,1,3), (5,2,8,2,1), (7,2,6,1,2)]:
    run(p, k, nmax, J, rmax, False)
# conjugate action (small ranges: chi(xi_j) needs many Frobenius powers)
for (p, k, nmax, J, rmax) in [(3,1,30,1,4), (3,1,20,2,1), (3,2,14,1,3), (3,2,12,2,1), (5,1,20,1,3),
                              (5,2,8,1,2), (2,2,16,2,2), (2,3,14,1,4), (3,3,14,1,2)]:
    run(p, k, nmax, J, rmax, True)
# decomposition into Dickson monomials
decomp(2, 3, 40); decomp(2, 4, 40); decomp(3, 2, 40); decomp(3, 3, 30); decomp(5, 2, 40); decomp(7, 2, 30)

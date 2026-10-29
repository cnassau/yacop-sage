# Checks the action on the Mui generators (Theorem 6.1, dickson.tex) against a
# direct computation in H^*(BV_k).  There tau_j = sum_i (M^-1)_{ji} y_i, where
# M = (x_i^(p^j)) is the Moore matrix.  Since reduced powers fix the y_i,
# P^r tau_j = sum_i P^r((M^-1)_{ji}) y_i, which is rewritten in the tau-basis
# via y_i = sum_j tau_j x_i^(p^j).  The result is compared with yacop's
# DicksonAlgebra.
#
# Uses the yacop in this checkout (the container's installed copy may be older).
# Run from the repository root:
#   ./yacop.sh -c "import sys; sys.path.insert(0, '$PWD'); from sage.all import *; import yacop
#   $(cat dickson-checks/mui_action.py)"
import sys
from yacop.modules.dickson import DicksonAlgebra
import itertools
def check(p, k, rmax):
    B = PolynomialRing(GF(p), ['x%d'%(i+1) for i in range(k)]); xs = B.gens()
    K = FractionField(B)
    M = matrix(K, k, k, lambda i,j: xs[i]**(p**j))
    Minv = M.inverse()
    Q = PolynomialRing(B,'X'); X=Q.gen()
    f = prod(X - sum(a*x for a,x in zip(v,xs)) for v in itertools.product(range(p),repeat=k))
    cpol = [f[p**i] for i in range(k)]
    PS = PowerSeriesRing(K, 't', default_prec=rmax+1); t = PS.gen()
    def Lam(r):
        r = K(r)
        sub = {x: x + t*x**p for x in xs}
        num = PS(B(r.numerator()).subs({x: x for x in xs}))
        def lam_poly(g):
            g = B(g); out = PS(0)
            for (ex, c) in g.dict().items():
                if not isinstance(ex, (tuple, list)) and not hasattr(ex, '__iter__'): ex = (ex,)
                term = PS(c)
                for x, e in zip(xs, ex):
                    term *= (x + t*x**p)**e
                out += term
            return out
        return lam_poly(r.numerator()) / lam_poly(r.denominator())
    D = DicksonAlgebra(p, k, generic=True)
    A = SteenrodAlgebra(p) if p > 2 else SteenrodAlgebra(2, generic=True)
    def to_poly(elem):
        out = {}
        for (key, cf) in elem:
            key = list(key) + [0]*(2*k - len(key))
            taus = key[0::2]; ds = key[1::2]
            assert sum(taus) == 1
            j = taus.index(1)
            val = K(cf)
            for num, e in enumerate(ds, start=1):
                val *= K(cpol[k - num])**e
            out[j] = out.get(j, K(0)) + val
        return out
    ok = bad = 0
    for j in range(k):
        tau_j = D._monomial_gen(2*j + 1)
        lams = [Lam(Minv[j, i]) for i in range(k)]
        for r in range(1, rmax+1):
            direct = {}
            for jp in range(k):
                v = sum(lams[i][r] * xs[i]**(p**jp) for i in range(k))
                if v != 0: direct[jp] = v
            code = {a: b for a, b in to_poly(A.P(r) * tau_j).items() if b != 0}
            if direct == code: ok += 1
            else:
                bad += 1; print("  mismatch p=%d k=%d j=%d P^%d" % (p, k, j, r))
    print("p=%d k=%d: P^r on tau_j vs direct: %d ok, %d bad" % (p, k, ok, bad)); sys.stdout.flush()
check(3, 1, 4)
check(3, 2, 4)
check(5, 2, 3)
check(2, 2, 6)

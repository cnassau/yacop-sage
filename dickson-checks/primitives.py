# Checks (*) for the Milnor primitives P(0,...,0,1), which act as the derivation
# x -> x^(p^j), on invariant Peterson elements.  Table 1, row 6.
#
# Run:  ./yacop.sh -c "$(cat dickson-checks/primitives.py)"
from sage.all import *
import sys
def binp(p,a,b): return GF(p)(binomial(a,b)) if b>=0 else GF(p)(0)
def run(p, k, nmax, j):
    R = PolynomialRing(GF(p), ['x%d'%(i+1) for i in range(k)]); xs = R.gens()
    gt = [(-1)**m*binp(p,-(p-1)*m,m) for m in range(nmax+ (p**j-1)//(p-1) + 2)]
    cache = {}
    def om(n):
        if n not in cache:
            cache[n] = sum((prod(gt[a] for a in e)*prod(x**((p-1)*a) for x,a in zip(xs,e)) for e in IntegerVectors(n,k)), R(0))
        return cache[n]
    d = (p**j-1)//(p-1); N = p**j
    good=bad=0
    for n in range(nmax+1):
        w = om(n)
        if w == 0 or w.subs({xs[0]:xs[0]+xs[1]}) != w: continue
        lhs = sum(x**(p**j)*w.derivative(x) for x in xs)   # P^{Delta_j} is the derivation x -> x^{p^j}
        a = binp(p, (p-1)*(n+d), N)
        if lhs == a*om(n+d): good+=1
        else:
            bad+=1; print("   MISMATCH p=%d k=%d n=%d Delta_%d" % (p,k,n,j))
    print("P(Delta_%d) p=%d k=%d nmax=%d: good=%d bad=%d" % (j,p,k,nmax,good,bad)); sys.stdout.flush()
run(3,3,26,2)
run(2,3,30,2); run(2,3,24,3); run(2,4,20,2)
run(5,2,30,2)

r"""
A tensor product of an exterior algebra and a polynomial algebra. Used in the dual Steenrod algebra and the Dickson-Mui algebras.

AUTHORS: - Christian Nassau (2011-05-13: version 1.0)

CLASS DOCUMENTATION:
"""

# *****************************************************************************
#       Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#  Distributed under the terms of the GNU General Public License (GPL)
# *****************************************************************************

from yacop.utils.region import region
from yacop.utils.gradings import YacopGrading
from yacop.utils.set_of_elements import SetOfMonomials, SetOfElements
from yacop.modules.algebra_base import SteenrodAlgebraBase
from yacop.categories import YacopLeftModuleAlgebras, YacopGradedObjects
from yacop.categories.functors import suspension, SuspendedObjectsCategory
from yacop.categories.functors import truncation, TruncatedObjectsCategory
from sage.rings.infinity import Infinity
from sage.combinat.free_module import CombinatorialFreeModule
from sage.structure.sage_object import SageObject
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.sets.set import Set
from sage.sets.family import LazyFamily, Family
from sage.categories.examples.infinite_enumerated_sets import NonNegativeIntegers
from sage.categories.all import AlgebrasWithBasis
from sage.categories.cartesian_product import cartesian_product
from sage.sets.integer_range import IntegerRange
from sage.algebras.all import SteenrodAlgebra, Sq
from sage.rings.integer import Integer
from sage.structure.formal_sum import FormalSum, FormalSums
from sage.structure.unique_representation import UniqueRepresentation
from sage.arith.all import is_prime
from yacop.utils.finite_graded_set import InfiniteGradedSet
from yacop.utils.bitstuff import N0

"""
  Pickling hack::

    sage: import __main__
    sage: from yacop.modules.xitauring import *
    sage: __main__.XiTauRing = XiTauRing
"""


class XiTauRing(CombinatorialFreeModule, UniqueRepresentation):

    r"""
    TESTS::

      sage: from yacop.modules.xitauring import XiTauRing
      sage: X=XiTauRing(5) ; X
      <<xitau ring for prime 5, names=('xi[{idx}]', 'tau[{idx}]')>>
      sage: X is XiTauRing(5)
      True
      sage: X.an_element()
      2 + 2*xi[2] + 3*xi[2]**2
      sage: X.monomial((9,(0,0,4)))
      tau[0]*tau[3]*xi[3]**4
      sage: latex(X.monomial((2,(1,2))))
      \tau_{1}\xi_{1}\xi_{2}^{2}
      sage: TestSuite(X).run()

    """

    @staticmethod
    def __classcall__(
        cls, prime, numxi=None, numtau=None, degrees=None, names=None, latexnames=None
    ):
        if numxi is None:
            numxi = Infinity
        if numtau is None:
            numtau = Infinity
        if names is None:
            names = ("xi[{idx}]", "tau[{idx}]")
        if latexnames is None:
            latexnames = ("\\xi_{{{idx}}}", "\\tau_{{{idx}}}")
        return super(XiTauRing, cls).__classcall__(
            cls, prime, numxi, numtau, degrees, tuple(names), tuple(latexnames)
        )

    def __init__(self, prime, numxi, numtau, degrees, names, latexnames):
        self._prime = prime
        self.numxi = numxi
        self.numtau = numtau
        self.names = names
        self.latexnames = latexnames
        self._degrees = degrees
        # hack: create a tiny pseudo basis for the test suite
        b = []
        for e in range(0, 8):
            for u in range(0, 3):
                for v in range(0, 3):
                    b.append((e, (u, v)))
        CombinatorialFreeModule.__init__(
            self, GF(prime), Family(b), category=AlgebrasWithBasis(GF(prime))
        )

    def _repr_(self):
        return "<<xitau ring for prime %d, names=%s>>" % (self._prime, self.names)

    def _repr_term(self, elem, islatex=False):
        e, p = elem
        ans = []
        if islatex:
            tau = self.latexnames[1]
            xi = self.latexnames[0]
            expo = "%s^{%d}"
            exponeg = expo
            times = ""
        else:
            tau = self.names[1]
            xi = self.names[0]
            expo = "%s**%d"
            exponeg = "%s**(%d)"
            times = "*"
        for (idx, digit) in zip(N0(), Integer(e).digits(2)):
            if digit == 1:
                deg = (
                    abs(self._degrees[2 * idx][1]) if not self._degrees is None else -1
                )
                ans.append(tau.format(idx=idx, deg=deg))
        for (idx, exp) in zip(N0(), p):
            if exp != 0:
                deg = self._degrees[2 * idx + 1][0] if not self._degrees is None else -1
                var = xi.format(deg=deg, idx=idx + 1)
                if exp != 1:
                    if exp > 0:
                        ans.append(expo % (var, exp))
                    else:
                        ans.append(exponeg % (var, exp))
                else:
                    ans.append(var)

        if len(ans):
            return times.join(ans)
        return "1"

    def _latex_term(self, elem):
        return self._repr_term(elem, islatex=True)

    def one_basis(self):
        return (0, ())

    def product_on_basis(self, a, b):
        e, p = a
        f, q = b
        if 0 != (e & f):
            return self.zero()
        # FIXME: sign correction needed
        if len(p) < len(q):
            p, q = q, p
        q2 = [x for x in q] + [0 for x in p]
        r = [x + y for (x, y) in zip(p, q2)]
        return self.monomial(((e | f), tuple(r)))

    class GeneratorList(object):
        """
        List of generators for a XiTauRing object-
        """

        def __init__(self, rng):
            self.r = rng
            self.idx = 0

        def __iter__(self):
            return XiTauRing.GeneratorList(self.r)

        def __next__(self):
            r = self.r
            i = self.idx
            self.idx = i + 1
            i = i ^ 1
            num = (i ^ (i & 1)) >> 1
            if num >= r.numxi and num > r.numtau:
                raise StopIteration
            if i & 1:
                if num >= r.numtau:
                    return next(self)
                return r.monomial((1 << num, ()))
            else:
                if num >= r.numxi:
                    return next(self)
                d = tuple([0 if x < num else 1 for x in range(0, num + 1)])
                return r.monomial((0, d))

    def gens(self):
        """
        Possibly infinite iterator that interleaves the xi and tau.

        TESTS::

            sage: from yacop.modules.xitauring import XiTauRing
            sage: X = XiTauRing(5)
            sage: from itertools import islice
            sage: list(islice(X.gens(),10))
            [tau[0], xi[1], tau[1], xi[2], tau[2], xi[3], tau[3], xi[4], tau[4], xi[5]]
            sage: X = XiTauRing(3,names=["a{idx}","b{idx}"],numxi=2,numtau=1)
            sage: list(X.gens())
            [b0, a1, a2]
            sage: X = XiTauRing(2,names=["x{idx}","t"],numxi=4,numtau=0)
            sage: list(X.gens())
            [x1, x2, x3, x4]

        """
        return XiTauRing.GeneratorList(self)

    def _monomial_gen(self, idx, expo=1):
        if idx & 1:
            return self.monomial((1 << (idx >> 1), ()))
        idx = idx >> 1
        return self.monomial(
            (0, tuple([0 if x < idx else expo for x in range(1, idx + 1)]))
        )

    def _genpower(self, gen, exp):
        if exp == 0:
            return self.one()
        if exp == 1:
            return gen
        (((q, p), cf),) = gen
        return self._from_dict({(q, tuple(exp * _ for _ in p)): cf})

    class Element(CombinatorialFreeModule.Element):
        """
        TESTS::

            sage: from yacop.modules.xitauring import XiTauRing
            sage: X = XiTauRing(5,names=["a{idx}","b{idx}"],numxi=2,numtau=1)
            sage: b0,a1,a2 = list(X.gens())
            sage: a1**17
            a1**17
            sage: (a1+a2)**3
            a2**3 + 3*a1*a2**2 + 3*a1**2*a2 + a1**3
            sage: (a1+b0)**18
            a1**18 + 3*b0*a1**17
        """

        pass


# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

r"""
A base class for algebras over the Steenrod algebra.

   TESTS::

        sage: from yacop.modules.algebra_base import *
        sage: # we implement the cohomology of "BZp smash BZp"
        sage: class Testclass(SteenrodAlgebraBase):
        ....:       def __init__(this,p,category=None):
        ....:           # must admit the "category" keyword for suspendability
        ....:           R.<x,a,y,b> = PolynomialRing(GF(p),"x,a,y,b")
        ....:           I = R.ideal([a**2,b**2])
        ....:           degs = lambda idx : (1,-1,0) if (idx&1) else (2,0,0)
        ....:           SteenrodAlgebraBase.__init__(this,R,[degs(n) for n in (0,..,3)],I,
        ....:                                        SteenrodAlgebra(p),category=category)
        ....:       def _left_steenrod_coaction_milnor_gen(this,idx,maxq,maxp):
        ....:           from yacop.utils.bitstuff import Delta
        ....:           if 1&idx:
        ....:              # coact(a) = sum tau_k x^(p^k)
        ....:              yield this._coaction_tensor(this.gens()[idx],0,())
        ....:              for (i,digit) in zip(range(0,1000),reversed(bin(maxq)[2:])):
        ....:                 if digit=='1':
        ....:                    res = this.gens()[idx-1]**(this._prime**i)
        ....:                    yield this._coaction_tensor(res,1<<i,())
        ....:           else:
        ....:              # coact(x) = sum xi_k x^(p^k)
        ....:              for (i,exp) in zip(range(0,1000),[1,]+list(maxp)):
        ....:                 if exp>0:
        ....:                    res = this.gens()[idx]**(this._prime**i)
        ....:                    yield this._coaction_tensor(res,0,Delta(i))
        ....:       def _bbox(this):
        ....:           return region(tmin=0,s=0,emax=0)
        ....:       def _can_test_pickling(this):
        ....:           return False # pickling not implemented
        sage: X=Testclass(3)
        sage: X.category()
        Category of yacop left module algebras over mod 3 Steenrod algebra, milnor basis

        sage: # a hack to fix pickling of TestClass objects
        sage: import __main__
        sage: __main__.Testclass = Testclass

        sage: TestSuite(X).run()
        sage: X.inject_variables()
        Defining x, a, y, b
        sage: for u in X.gens():
        ....:     print(u,u.t,u.e,u.s)
        x 2 0 0
        a 1 -1 0
        y 2 0 0
        b 1 -1 0
        sage: sorted(X.graded_basis(region(tmax=4)))
        [1, b, y, y*b, y^2, a, a*b, a*y, a*y*b, x, x*b, x*y, x*a, x*a*b, x^2]
        sage: for u in [x*y-y*x,a*b+b*a,x*a-a*x,x*b-b*x,y*a-a*y,a**2,b**2]:
        ....:    assert u==X.zero()
        sage: a**2 == 0
        True
        sage: for idx in (0,..,3):
        ....:    print(X.gens()[idx])
        ....:    for smd in X._left_steenrod_coaction_milnor_gen(idx,0b10011,(1,0,2,2)):
        ....:         print(" ->",smd)
        x
        -> (x)*1
        -> (x^3)*xi(1)
        -> (x^27)*xi(0,0,1)
        -> (x^81)*xi(0,0,0,1)
        a
        -> (a)*1
        -> (x)*tau(1)
        -> (x^3)*tau(0,1)
        -> (x^81)*tau(0,0,0,0,1)
        y
        -> (y)*1
        -> (y^3)*xi(1)
        -> (y^27)*xi(0,0,1)
        -> (y^81)*xi(0,0,0,1)
        b
        -> (b)*1
        -> (y)*tau(1)
        -> (y^3)*tau(0,1)
        -> (y^81)*tau(0,0,0,0,1)
        sage: A = SteenrodAlgebra(3)
        sage: P,Q = A.P, A.Q
        sage: [Q(i)*a for i in (0,..,3)]
        [x, x^3, x^9, x^27]
        sage: [Q(i)*b for i in (0,..,3)]
        [y, y^3, y^9, y^27]
        sage: Q(0)*(a*b) + a*y - x*b
        0
        sage: [Q(i)*(Q(i)*(a*b)) for i in (0,..,3)]
        [0, 0, 0, 0]
        sage: matrix([[Q(i)*(Q(j)*(a*b)) + Q(j)*(Q(i)*(a*b)) for i in (0,..,3)] for j in (0,..,3)])
        [0 0 0 0]
        [0 0 0 0]
        [0 0 0 0]
        [0 0 0 0]
        sage: [Q(i)*(a*b) for i in (0,..,3)]
        [2*a*y + x*b, 2*a*y^3 + x^3*b, 2*a*y^9 + x^9*b, 2*a*y^27 + x^27*b]
        sage: [P(i)*x**26 for i in (0,..,7)]
        [x^26, 2*x^28, x^30, 2*x^32, x^34, 2*x^36, x^38, 2*x^40]
        sage: [P(i)*(x*y) for i in (0,..,7)]
        [x*y, x*y^3 + x^3*y, x^3*y^3, 0, 0, 0, 0, 0]
        sage: for i in (0,..,6):
        ....:    print("P(%d)"%i,":","|".join(["%8s"%(P(i)*(x**j),) for j in (0,..,9)]))
        P(0) :        1|       x|     x^2|     x^3|     x^4|     x^5|     x^6|     x^7|     x^8|     x^9
        P(1) :        0|     x^3|   2*x^4|       0|     x^6|   2*x^7|       0|     x^9|  2*x^10|       0
        P(2) :        0|       0|     x^6|       0|       0|     x^9|       0|       0|    x^12|       0
        P(3) :        0|       0|       0|     x^9|    x^10|    x^11|  2*x^12|  2*x^13|  2*x^14|       0
        P(4) :        0|       0|       0|       0|    x^12|  2*x^13|       0|  2*x^15|    x^16|       0
        P(5) :        0|       0|       0|       0|       0|    x^15|       0|       0|  2*x^18|       0
        P(6) :        0|       0|       0|       0|       0|       0|    x^18|    x^19|    x^20|       0

        sage: for i in (0,..,6):
        ....:    print("P(%d)"%i,":","|".join(["%8s"%(P(i)*(b*y**j),) for j in (0,..,9)]))
        P(0) :        b|     y*b|   y^2*b|   y^3*b|   y^4*b|   y^5*b|   y^6*b|   y^7*b|   y^8*b|   y^9*b
        P(1) :        0|   y^3*b| 2*y^4*b|       0|   y^6*b| 2*y^7*b|       0|   y^9*b|2*y^10*b|       0
        P(2) :        0|       0|   y^6*b|       0|       0|   y^9*b|       0|       0|  y^12*b|       0
        P(3) :        0|       0|       0|   y^9*b|  y^10*b|  y^11*b|2*y^12*b|2*y^13*b|2*y^14*b|       0
        P(4) :        0|       0|       0|       0|  y^12*b|2*y^13*b|       0|2*y^15*b|  y^16*b|       0
        P(5) :        0|       0|       0|       0|       0|  y^15*b|       0|       0|2*y^18*b|       0
        P(6) :        0|       0|       0|       0|       0|       0|  y^18*b|  y^19*b|  y^20*b|       0

        sage: from yacop.utils.region import region
        sage: #X._manual_test_left_conj_action(region(tmax=10))
        sage: X._manual_test_left_action(region(tmax=10))
        284 non-zero multiplications checked



"""
# *****************************************************************************
#       Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#  Distributed under the terms of the GNU General Public License (GPL)
# *****************************************************************************

# pylint: disable=E0213

from yacop.utils.region import region
from yacop.utils.gradings import YacopGrading
from yacop.utils.finite_graded_set import FiniteGradedSet
from yacop.modules.module_base import SteenrodModuleBase
from yacop.categories import (
    YacopBimodules,
    YacopLeftModuleAlgebras,
    YacopRightModuleAlgebras,
    YacopBimoduleAlgebras,
    YacopGradedSets,
    YacopGradedObjects,
)
from yacop.categories.functors import suspension, SuspendedObjectsCategory
from yacop.categories.functors import truncation, TruncatedObjectsCategory
from sage.rings.infinity import Infinity
from sage.structure.sage_object import SageObject
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.sets.set import Set
from sage.sets.finite_enumerated_set import FiniteEnumeratedSet
from sage.sets.family import LazyFamily, Family
from sage.categories.examples.infinite_enumerated_sets import NonNegativeIntegers
from sage.categories.algebras_with_basis import AlgebrasWithBasis
from sage.sets.integer_range import IntegerRange
from sage.algebras.all import SteenrodAlgebra, Sq
from sage.rings.integer import Integer
from sage.structure.element import have_same_parent
from sage.structure.formal_sum import FormalSum, FormalSums
from sage.structure.unique_representation import UniqueRepresentation
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.categories.infinite_enumerated_sets import InfiniteEnumeratedSets
from sage.structure.parent import Parent
from sage.structure.element import Element
from sage.misc.classcall_metaclass import ClasscallMetaclass
from yacop.utils.finite_graded_set import InfiniteGradedSet
from sage.misc.lazy_format import LazyFormat
from sage.misc.abstract_method import abstract_method
from sage.misc.cachefunc import cached_method
from sage.functions.generalized import sgn
from sage.combinat.integer_vector_weighted import WeightedIntegerVectors
from yacop.utils.bitstuff import (
    qexp_to_bitmask,
    sign_correction,
    bitcount,
    Delta,
    N0,
    binom_modp,
)
import operator

# TODO: make this a cythoned class (e.g., check speed of
# A2Module(777).dimension())


class SteenrodAlgebraBasis(InfiniteGradedSet, UniqueRepresentation):

    """
    The basis key family of a SteenrodAlgebraBase object.
    """

    @staticmethod
    def __classcall_private__(cls, module):
        return super(SteenrodAlgebraBasis, cls).__classcall__(cls, module)

    def __init__(self, mod):
        self.module = mod
        InfiniteGradedSet.__init__(self)

    def bbox(self):
        return self.module._bbox()

    def degree(self, elem):
        return self.module._degree_on_basis(elem)

    def __iter__(self, reg=None):
        if reg is None:
            reg = region()
        tmin, tmax = reg.trange
        octs = self.module.octants()
        assert len(octs) == 1  # TODO: allow more than one octant
        tsign, esign, ssign = octs[0]
        from itertools import chain

        if tsign == +1:
            I = IntegerRange(Integer(0), tmax + 1)
            return chain.from_iterable(
                self._truncate_region(reg.intersect(region(t=n))) for n in I
            )
        else:
            I = IntegerRange(Integer(0), -tmin)
            return chain.from_iterable(
                self._truncate_region(reg.intersect(region(t=-n))) for n in I
            )

    def _truncate_region(self, reg):
        reg = reg.intersect(self.bbox())
        if reg.is_empty():
            return Set(())

        emin, emax = reg.erange
        smin, smax = reg.srange
        tmin, tmax = reg.trange
        octs = self.module.octants()
        assert len(octs) == 1  # TODO: allow more than one octant
        tsign, esign, ssign = octs[0]

        if False:
            # we need to deal with the case of the dickson algebras, for example,
            # where tsign = +1, but there are finitely many negative dimensional
            # classes, so tmin < 0
            # this whole codeblock seems to be overly complicated: a simple
            # test reg.intersect(self.bbox()).not_empty() might be better (?)
            bbx = self.bbox()
            if tsign <= 0:
                tmax = min(bbx.tmax, tmax)
            if tsign >= 0:
                tmin = max(bbx.tmin, tmin)
            if esign <= 0:
                emax = min(bbx.emax, emax)
            if esign >= 0:
                emin = max(bbx.emin, emin)
            if ssign <= 0:
                smax = min(bbx.smax, smax)
            if ssign >= 0:
                smin = max(bbx.smin, smin)
            if (tsign > 0 and tmax < bbx.tmin) or (tsign < 0 and tmin > bbx.tmax):
                return Set(())
            if (esign > 0 and emax < bbx.emin) or (esign < 0 and emin > bbx.emax):
                return Set(())
            if (ssign > 0 and smax < bbx.smin) or (ssign < 0 and smin > bbx.smax):
                return Set(())

        if reg.contains(self.bbox()):
            return self

        # if (tsign,tmax) == (+1,Infinity) or (tsign,tmin) == (-1,-Infinity):
        # return self

        # TODO: treat the general case
        # assert (tsign>0 and tmax<Infinity) or (tsign<0 and tmin>-Infinity)
        effdegrees = self.module._t_degrees(max(abs(tmin), abs(tmax)))
        negeffdegrees = [-x for x in effdegrees]
        it = iter(self.module._max_exponents())
        maxexpos = [next(it) for x in zip(effdegrees)]
        ans = []
        for t in range(tmin, tmax + 1):
            if t >= 0:
                T, E = t, effdegrees
            else:
                T, E = -t, negeffdegrees
            for u in SteenrodAlgebraBasis.WeightedIntegerVectors(T, E, maxexpos):
                if not self.module._is_basis_key(u):
                    continue
                u = list(u)
                while len(u) > 0 and u[len(u) - 1] == 0:
                    u.pop()
                if reg.contains(self.degree(u)):
                    ans.append(tuple(u))
        return Set(ans)

    @staticmethod
    def WeightedIntegerVectors(T, E, maxexpos):
        """
        a variant of Sage's WeightedIntegerVectors that can cope with negative weights as long as
        there are limits on them

        Currently the limits on the negative exponents must be one.

        TESTS::
            sage: from yacop.modules.algebra_base import SteenrodAlgebraBasis
            sage: wiv = SteenrodAlgebraBasis.WeightedIntegerVectors
            sage: sorted(wiv(7,[2,-1,5],[Infinity,1,Infinity]))
            [(1, 0, 1), (4, 1, 0)]
            sage: sorted(wiv(30,(-1,36,-5,48,-17,52),(1,20,1,20,1,20)))
            [(0, 0, 1, 0, 1, 1), (1, 0, 0, 1, 1, 0), (1, 1, 1, 0, 0, 0)]

        """
        from sage.modules.free_module_element import vector
        from sage.combinat.subset import Subsets

        # print "WeightedIntegerVectors", (T,E,maxexpos)
        l = len(E)
        negidx = [i for i in range(l) if E[i] < 0 and maxexpos[i] > 0]
        posidx = [i for i in range(l) if E[i] > 0]
        posvecs = [vector([1 if i == j else 0 for j in range(l)]) for i in posidx]
        maxneg = sum(E[i] * maxexpos[i] for i in negidx)
        posweights = [E[i] for i in posidx]
        for negbits in Subsets(negidx):
            negsum = sum(E[i] for i in negbits)
            negvec = vector([1 if i in negbits else 0 for i in range(l)])
            for w in WeightedIntegerVectors(T - negsum, posweights):
                posvec = sum(a * b for (a, b) in zip(w, posvecs))
                ans = negvec + posvec
                if all(i <= j for (i, j) in zip(ans, maxexpos)):
                    yield ans

    def _repr_(self):
        return "basis key family of %s" % self.module

    def _test_pickling(self, tester=None, **options):
        try:
            if not self.module._can_test_pickling():
                return
        except:
            return super(SteenrodAlgebraBasis, self)._test_pickling(tester, **options)


class SteenrodAlgebraBase(SteenrodModuleBase):

    """
    dummy doc, replaced below
    """

    @staticmethod
    def __classcall_private__(
        cls,
        ring,
        degrees,
        ideal=None,
        algebra=None,
        left_action=None,
        right_action=None,
        category=None,
    ):
        b = ring.base_ring()
        p = b.characteristic()
        assert b is GF(p)
        if algebra is None:
            algebra = SteenrodAlgebra(p)
        if left_action is None:
            left_action = True
        if right_action is None:
            right_action = False
        assert left_action or right_action
        return super(SteenrodAlgebraBase, cls).__classcall__(
            cls,
            ring,
            degrees,
            ideal,
            algebra=algebra,
            left_action=left_action,
            right_action=right_action,
            category=category,
        )

    def __init__(
        self,
        ring,
        degrees,
        ideal=None,
        algebra=None,
        left_action=True,
        right_action=False,
        category=None,
    ):

        self._R = ring
        self._I = ideal
        self._gens = ring.gens()
        # can be overriden in derived classes (eg for negative exponents)
        self._genpower = lambda g, e: g ** e

        if isinstance(degrees, list):
            degrees = Family(degrees)
        self._degrees = degrees
        if ideal is not None:
            self._gb = ideal.groebner_basis()
            self._Q = ring.quotient(ideal)
            # check that the defining relations are homogeneous
            for u in ideal.gens():
                udeg = None
                for m in u.monomials():
                    deg = self._degree_on_basis(m.exponents()[0])
                    if udeg is None:
                        udeg = deg
                    else:
                        if deg != udeg:
                            raise ValueError(
                                "ideal not homogeneous: %s has terms of degree %s and %s"
                                % (u, deg, udeg)
                            )

        if category is None:
            if left_action:
                if right_action:
                    category = YacopBimoduleAlgebras(algebra)
                else:
                    category = YacopLeftModuleAlgebras(algebra)
            else:
                category = YacopRightModuleAlgebras(algebra)

        self.__steenrod_algebra = category.base_ring()

        SteenrodModuleBase.__init__(self, SteenrodAlgebraBasis(self), category=category)

    # reimplement "one" because suspensions are not rings
    def one(self):
        return self.monomial(self.one_basis())

    # reimplement product because suspensions are no longer algebras with basis
    def product(self, left, right):
        return self.linear_combination(
            (self.product_on_basis(mon_left, mon_right), coeff_left * coeff_right)
            for (mon_left, coeff_left) in left.monomial_coefficients().items()
            for (mon_right, coeff_right) in right.monomial_coefficients().items()
        )

    def _is_sorted_by_t_degrees(self):
        return False

    def _max_exponents(self):
        for (t, e, s) in self._degrees:
            if e & 1:
                yield 2
            else:
                yield Infinity

    def _t_degrees(self, tmax):
        """
        return the t-degrees with absolute values not bigger than ``tmax``
        """
        if self._is_sorted_by_t_degrees():
            ans = []
            for (t, e, s) in self._degrees:
                if abs(t) > tmax:
                    return ans
                ans.append(t)
        return [t for (t, e, s) in self._degrees]

    @cached_method
    def octants(self):
        assert self._degrees.is_finite()
        from sage.combinat.posets.posets import Poset

        def pocom(a, b):
            t1, e1, s1 = a
            t2, e2, s2 = b
            if (t1 in (t2, 0)) and (e1 in (e2, 0)) and (s1 in (s2, 0)):
                return True
            return False

        X = Poset(([(sgn(t), sgn(e), sgn(s)) for (t, e, s) in self._degrees], pocom))
        return [list(u) for u in X.maximal_elements()]

    def _test_generator_degrees(self, tester=None, **options):
        from sage.misc.sage_unittest import TestSuite
        from itertools import islice

        is_sub_testsuite = tester is not None
        tester = self._tester(tester=tester, **options)
        if self._is_sorted_by_t_degrees():
            gdegs = [g[0] for g in islice(self._degrees, 30)]
            gd = gdegs
            for u in gd:
                if u < 0:
                    gd = [-u for u in gdegs]
                    break
            for (u, v) in zip(gd, gd[1:]):
                tester.assertTrue(
                    u <= v,
                    LazyFormat(
                        "generators not sorted by internal degree, degrees= %s..."
                    )
                    % (gdegs,),
                )
        octs = self.octants()
        for (t, e, s) in islice(self._degrees, 30):
            if 0 != (e & 1):
                # allow mismatch for exterior generators
                continue
            ok = False
            for (ts, es, ss) in octs:
                if (sgn(t) in (ts, 0)) and (sgn(e) in (es, 0)) and (sgn(s) in (ss, 0)):
                    ok = True
                    break
            tester.assertTrue(
                ok,
                LazyFormat("generator degree (%d,%d,%d) not in one of the octants %s")
                % (t, e, s, octs),
            )

    def _repr_(self):
        R = self._R
        if self._I is not None:
            R = self._Q
        return "%s with action by %s" % (R, self.__steenrod_algebra)

    @abstract_method(optional=False)
    def _bbox(self):
        """
        bounding box of this module
        """

    def one_basis(self):
        return ()

    def gens(self):
        rge = list(range(0, len(self._gens)))
        return [self.monomial(tuple((0 if u != v else 1) for u in rge)) for v in rge]

    def _monomial(self, exponents):
        e = list(exponents)
        while len(e) and e[len(e) - 1] == 0:
            e.pop()
        return super(SteenrodAlgebraBase, self)._monomial(tuple(e))

    def variable_names(self):
        return self._R.variable_names()

    def _edegree_signature(self, elem):
        ans = 0
        msk = 1
        for (u, dg) in zip(elem, self._degrees):
            if (u & 1) and (dg[1] & 1):
                ans = ans | msk
            msk = msk << 1
        return ans

    def _is_basis_key(self, ans):
        for (idx, exp) in zip(N0(), ans):
            if self.__gen_is_odd(idx) and exp > 1:
                return False
        return True

    def product_on_basis(self, left, right):
        # from yacop.utils.bitstuff import n0
        msk = self._edegree_signature
        sgn = -1 if sign_correction(msk(left), msk(right)) else 1
        if len(left) < len(right):
            left, right = right, left
        rg = [u for u in right] + [0 for u in left]
        ans = [u + v for (u, v) in zip(left, rg)]
        if not self._is_basis_key(ans):
            return self.zero()
        ans = self.monomial(ans)
        if sgn == 1:
            return ans
        return ans.map_coefficients(lambda x: sgn * x)

    def _mul_(self, other, switch_sides=False):
        if other in self.grading().suspenders():
            return other._act_on_(self, not switch_sides)
        ans = super(SteenrodModuleBase, self)._mul_(other, switch_sides=switch_sides)
        return self._reduce(ans)

    def _degree_on_basis(self, exponents):
        xt, xe, xs = 0, 0, 0
        for (e, (wt, we, ws)) in zip(exponents, self._degrees):
            xt = xt + e * wt
            xs = xs + e * ws
            xe = xe + e * we
        return region(t=xt, e=xe, s=xs)

    def __to_R(self, exponents):
        return self._R.prod(
            [self._genpower(g, e) for (g, e) in zip(self._gens, exponents)]
        )

    def _reduce(self, elem):
        """
        Reduce an element of ``self`` modulo the defining ideal.
        """
        if self._I is None:
            return elem
        # FIXME: this code does most likely *not* work for a general
        # graded commutative algebra unless the prime is two.
        # we need to copy the code from rings/polynomial/multi_polynomial_element.py
        # and use sign-adjusted methods there.
        # TODO: create a doctest that illustrates/tests this problem
        x = self._R.sum(
            cf * self.__to_R(exponents)
            for (exponents, cf) in elem.monomial_coefficients().items()
        )
        y = self._Q(x).lift()
        ans = []
        for (m, c) in zip(y.exponents(), y.coefficients()):
            ans.append((m, c))
        return self._from_dict(dict(ans))

    def _repr_term(self, exponents):
        x = self.__to_R(exponents)
        return x._repr_()

    def _latex_term(self, exponents):
        x = self.__to_R(exponents)
        return x._latex_()

    class _coaction_tensor(SageObject):

        """
        private helper class that represents a tensor ``algelem * tau(...) * xi(...)``

        TESTS::

           sage: from yacop.modules.algebra_base import *
           sage: T = SteenrodAlgebraBase._coaction_tensor
           sage: from yacop.modules.dual_steenrod_algebra import DualSteenrodAlgebra
           sage: D = DualSteenrodAlgebra(5)
           sage: D.inject_variables()
           Defining xi, tau
           sage: a=T(xi[2],5,(3,0,1,0)) ; a
           (xi[2])*tau(1,0,1)*xi(3,0,1)
           sage: b=T(tau[1],2,(7,1)) ; b
           (tau[1])*tau(0,1)*xi(7,1)
           sage: c=T(xi[4],8,(0,0,1)) ; c
           (xi[4])*tau(0,0,0,1)*xi(0,0,1)
           sage: a*b
           [(4*tau[1]*xi[2])*tau(1,1,1)*xi(10,1,1)]
           sage: b*a
           [(4*tau[1]*xi[2])*tau(1,1,1)*xi(10,1,1)]
           sage: a*a
           []
           sage: b*b
           []
           sage: a*c
           [(xi[2]*xi[4])*tau(1,0,1,1)*xi(3,0,2)]
           sage: c*a
           [(xi[2]*xi[4])*tau(1,0,1,1)*xi(3,0,2)]
           sage: b*c
           [(tau[1]*xi[4])*tau(0,1,0,1)*xi(7,1,1)]
           sage: c*b
           [(tau[1]*xi[4])*tau(0,1,0,1)*xi(7,1,1)]
           sage: r,q,p=a
           sage: print(r,q,tuple(p))
           xi[2] 5 (3, 0, 1)
        """

        def __init__(self, algelem, qmask, pvect):
            self.r = algelem
            self.q = qmask
            self.p = self._vector_add(pvect, ())

        def _repr_(self):
            if self.q < 0:
                digs = [
                    "1" if u == 0 else "0" for u in Integer(-1 - self.q).digits(2)
                ] + ["1", "..."]
            else:
                digs = ["%d" % u for u in Integer(self.q).digits(2)]
            ans = [
                "(%s)" % self.r,
            ]
            bns = []
            if len(digs):
                bns.append("tau(%s)" % ",".join(digs))
            if len(self.p):
                bns.append("xi(%s)" % (",".join("%d" % u for u in self.p)))
            if len(bns) == 0:
                bns = [
                    "1",
                ]
            return "*".join(ans + bns)

        @staticmethod
        def _vector_add(s1, s2):
            a, b = list(s1), list(s2)
            v1 = list(a) + [0 for u in b]
            v2 = list(b) + [0 for u in a]
            w = [u + v for (u, v) in zip(v1, v2)]
            while len(w) and w[len(w) - 1] == 0:
                w.pop()
            return w

        def __mul__(left, right):
            # print "__mul__(%s,%s)" % (left,right)
            if 0 != (left.q & right.q):
                return []
            w = left._vector_add(left.p, right.p)
            cls = left.__class__
            P = left.r.parent()
            r = P.product(left.r, right.r)
            if 0 == len([k for (k, cf) in r if cf]):
                # product is zero
                return []
            sgn = -1 if 0 != (1 & right.r.e & bitcount(left.q)) else 1
            if sign_correction(left.q, right.q):
                sgn = -sgn
            if sgn < 0:
                r = -r
            # print "(r,left.q,right.q)=(%s,%s,%s)" % (r,left.q,right.q)
            return [
                cls(r, left.q | right.q, w),
            ]

        def __iter__(self):
            return iter([self.r, self.q, self.p])

        def __cmp__(self, other):
            """
            A cmp method to make sorting of _coaction_tensor objects
            independent of the object id (used in doctests).
            """
            return cmp(str(self), str(other))

        def filter(self, maxq, maxp, left_factor=True):
            if (self.q & maxq) != self.q:
                return []
            qrem = maxq ^ self.q
            prem = self._vector_add(maxp, (-u for u in self.p))
            if not all(u >= 0 for u in prem):
                return []
            a, b = qrem, self.q
            if not left_factor:
                a, b = b, a
            # r = -self.r if sign_correction(a,b) else self.r
            return [
                self.__class__(self.r, qrem, prem),
            ]

    # FIXME: add support for the conjugate action

    def _left_steenrod_coaction_milnor_gen(self, idx, maxQ, maxP):
        raise NotImplementedError

    def _right_steenrod_coaction_milnor_gen(self, idx, maxQ, maxP):
        raise NotImplementedError

    def _act_from_coact(self, actfunc, a, m):
        if not self._yacop_base_ring.is_generic():
            e, r = 0, a
        else:
            e, r = a
            e = qexp_to_bitmask(e)
            r = tuple(r)
        ans = []
        for (res, qmsk, pexp) in actfunc(m, e, r):
            if qmsk == e and tuple(pexp) == r and not res.is_zero():
                bc = bitcount(e)

                # sign change because we rearrange bocksteins and tau as in
                #  Q1 ... Qn  t1 ... tn  <-> Q1t1 ... Qntn
                sgn = -1 if (2 & bc) else 1

                # print "_act_from_coact(%s,%s): (e,res)=(%s,%s)" %(a,m,e,res)
                # TODO: add doctest for this sign change
                if (bc & 1) == 1 and (res.e & 1) == 1:
                    sgn = -sgn
                ans.append(res if sgn > 0 else -res)
        return self.sum(ans)

    def left_steenrod_action_milnor(self, a, m):
        return self._act_from_coact(self._left_coaction_on_basis, a, m)

    def right_steenrod_action_milnor(self, m, a):
        return self._act_from_coact(self._right_coaction_on_basis, a, m)

    def __gen_is_odd(self, idx):
        if self._degrees[idx][1] & 1:
            return True
        return False

    def _factor_key(self, expos, maxp):
        """
        Factor a monomial as ``x_{i1}^(a1*p^u1) ... x_{in}^(an*p^un)``

        Negative exponents require special care, which is why we
        have the argument ``maxp``.

        TESTS::

            sage: from yacop.testing.testalgebra import Testclass1
            sage: X=Testclass1(3)
            sage: X.inject_variables()
            Defining x, a, y, b

            sage: # 7 = 1*1 + 2*3, 1=1*1, 3=1*3
            sage: X._factor_key((7,1,3,0), 3)
            [(0, 1, 0), (0, 2, 1), (1, 1, 0), (2, 1, 1)]

            sage: # b**2 == 0
            sage: X._factor_key((7,0,3,2), 3)
            []

            sage: # -7 = -1*3^2 + 2*1
            sage: X._factor_key((-7,0,3,1), 2)
            [(0, -1, 2), (0, 2, 0), (2, 1, 1), (3, 1, 0)]

            sage: # maxp = 2 forces -1 = -1*9 + 2*1 + 2*3
            sage: X._factor_key((-1,0,0,0), 2)
            [(0, -1, 2), (0, 2, 0), (0, 2, 1)]

            sage: # -764 = 1*1 + 2*9 + 1*27 + 2*81 + 2*243 + 1*729 + -1*2187
            sage: X._factor_key((-764,0,3,1), 2)
            [(0, -1, 7),
            (0, 1, 0),
            (0, 2, 2),
            (0, 1, 3),
            (0, 2, 4),
            (0, 2, 5),
            (0, 1, 6),
            (2, 1, 1),
            (3, 1, 0)]

        """
        ans = []
        for (idx, e) in zip(N0(), expos):
            if self.__gen_is_odd(idx) and e > 1:
                return []
            if e < 0:
                # negative exponent: add prime power that
                # is invariant under all P(..)
                u = maxp
                pow = self._prime ** u
                while e + pow < 0:
                    pow *= self._prime
                    u += 1
                ans.append((idx, -1, u))
                e = e + pow
            for (u, a) in zip(N0(), Integer(e).digits(self._prime)):
                if a > 0:
                    ans.append((idx, a, u))
        return ans

    def _ppower(self, elem, expo):
        ans = []
        for (k, v) in elem.monomial_coefficients().items():
            ans.append((tuple(u * expo for u in k), v))
        return self._from_dict(dict(ans))

    def _coaction_helper_single(self, actfunc, idx, a, u, maxq, maxp):
        """
        compute left or right coaction on ``x_{id}^(a*p^u)``
        """
        assert 0 < a and a < self._prime or a == -1
        ppow = self._prime ** u
        if a < 0:
            assert a == -1
            # negative exponents: these are guaranteed to be invariant under
            # the operation, so we only care about the initial summand
            # psi(x^{p^k}) = (whatever) * 1
            mq2, mp2 = 0, ()
            coa = actfunc(idx, mq2, mp2)
            # print "(a,u)=",(a,u),coa.__name__,list(actfunc(idx,mq2,mp2))
            # return

            for smd in coa:
                for _ in smd.filter(mq2, mp2):
                    res, qexp, pexp = smd
                    yield self._coaction_tensor(
                        self._ppower(res, -ppow), qexp, [ppow * u for u in pexp]
                    )
            return

        if u > 0:
            mq2 = 0
            mp2 = [exp // ppow for exp in maxp]
        else:
            mq2 = maxq
            mp2 = maxp
        coa = actfunc(idx, mq2, mp2)
        if a == 1 or a == -1:
            for smd in coa:
                for _ in smd.filter(mq2, mp2):
                    res, qexp, pexp = smd
                    yield self._coaction_tensor(
                        self._ppower(res, ppow), qexp, [ppow * u for u in pexp]
                    )
            return
        # print "\nexpo=",a,":",list(actfunc(idx,mq2,mp2))
        # a>1, use multinomial formula
        # print "\nmultinomials(",a,")
        # =",list(self._multinomials(iter(coa),self._prime,a))
        for (smd, restexpo, explst) in self._multinomials(iter(coa), self._prime, a):
            if restexpo == 0:
                # print "   :",explst, "->",smd
                for _ in smd.filter(maxq, maxp):
                    r, q, p = smd
                    yield self._coaction_tensor(
                        self._ppower(r, ppow), q, [ppow * u for u in p]
                    )

    def _multinomials(self, smds, prime, total):
        try:
            cursmd = next(smds)
            r, q, p = cursmd
        except StopIteration:
            yield self._coaction_tensor(self.one(), 0, ()), total, []
            return
        for (smd, tot2, elst) in self._multinomials(smds, prime, total):
            # r2,q2,p2 = smd
            maxexpo = tot2
            for expo in range(0, maxexpo + 1):
                coeff = binom_modp(self._prime, tot2, expo)
                nr, nq, np = smd
                yield self._coaction_tensor(
                    nr.map_coefficients(lambda x: coeff * x), nq, np
                ), tot2 - expo, elst + [
                    expo,
                ]
                nextpow = cursmd * smd
                if len(nextpow) == 0:
                    break
                smd = nextpow[0]

    def _coaction_helper(self, actfunc, fk, maxq, maxp):
        # print "co",actfunc,fk,maxq,maxp
        if len(fk) > 1:
            aux = self._coaction_helper(actfunc, fk[1:], maxq, maxp)
        else:
            aux = [
                self._coaction_tensor(self.one(), 0, ()),
            ]
        # print aux
        if len(fk) == 0:
            yield aux[0]
            return
        idx, a, u = fk[0]
        # print
        # "\nco_single(",idx,a,u,maxq,maxp,")=",list(self._coaction_helper_single(actfunc,idx,a,u,maxq,maxp)),"\n"
        for smd in aux:
            # print "smd=",smd
            for rem in smd.filter(maxq, maxp):
                rx, maxq2, maxp2 = rem
                # print "_coaction_helper_single
                # gives",list(self._coaction_helper_single(actfunc,idx,a,u,maxq2,maxp2))
                for osmd in self._coaction_helper_single(
                    actfunc, idx, a, u, maxq2, maxp2
                ):
                    # print "%s * %s = %s" % (osmd,smd,osmd*smd)
                    for reslt in osmd * smd:
                        yield reslt

    def _left_coaction_on_basis(self, a, maxq, maxp):
        return self._coaction_helper(
            self._left_steenrod_coaction_milnor_gen,
            self._factor_key(a, 0 if len(maxp) == 0 else max(maxp)),
            maxq,
            maxp,
        )

    def _right_coaction_on_basis(self, a, maxq, maxp):
        return self._coaction_helper(
            self._right_steenrod_coaction_milnor_gen,
            self._factor_key(a, 0 if len(maxp) == 0 else max(maxp)),
            maxq,
            maxp,
        )

    class Element(SteenrodModuleBase.Element):
        def __hash__(self):
            """
            elements should be hashable because we use sets in some of our test methods.
            """
            return hash(str(self))

        def __eq__(left, right):
            if not have_same_parent(left, right):
                from sage.structure.element import get_coercion_model

                try:
                    return get_coercion_model().bin_op(left, right, operator.eq)
                except TypeError:
                    return False
            else:
                left, right = left.reduce(), right.reduce()
                return super(SteenrodAlgebraBase.Element, left).__eq__(right)

        def __ne__(left, right):
            return not (left.__eq__(right))

        def __lt__(left, right):
            return super(SteenrodAlgebraBase.Element, left).__lt__(right)

        def __gt__(left, right):
            return super(SteenrodAlgebraBase.Element, left).__gt__(right)

        def __le__(left, right):
            return left.__lt__(right) or left.__eq__(right)

        def __ge__(left, right):
            return left.__gt__(right) or left.__eq__(right)

        def __disabled_cmp__(left, right):
            if not have_same_parent(left, right):
                from sage.structure.element import get_coercion_model

                try:
                    return get_coercion_model().bin_op(left, right, cmp)
                except TypeError:
                    return -1
            else:
                print(
                    (
                        type(left._monomial_coefficients),
                        type(right._monomial_coefficients),
                    )
                )
                left, right = left.reduce(), right.reduce()
                return super(SteenrodAlgebraBase.Element, left).__cmp__(right)

        def reduce(self):
            par = self.parent()
            return par._reduce(self)


SteenrodAlgebraBase.__doc__ = __doc__

# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

r"""
Gradings

Yacop deals with differential modules over the Steenrod algebra `A`. These
have three natural gradings `t`, `e` and `s`:

  - internal grading `t`, corresponding to the usual degree of `A`
  - external grading `e`, corresponding to the Bockstein grading of `A` (this is zero for `p=2`)
  - homological grading `s`, lowered by the internal differential

We use :meth:`YacopGrading` objects to represent such a grading::

   sage: from yacop.categories.functors import *
   sage: from yacop.utils.gradings import YacopGradingFromDict
   sage: dct = []
   sage: dct.append((region(t=1,e=0,s=3),(1,2,3)))
   sage: dct.append((region(t=2,e=1,s=1),(4,)))
   sage: dct.append((region(t=0,e=7,s=1),(5,6)))
   sage: G = YacopGradingFromDict(dct) ; G.__custom_name = "G" ; G
   G
   sage: G.bbox()
   region(0 <= e <= 7, 1 <= s <= 3, 0 <= t <= 2)
   sage: G.basis(region(tmin=1))
   {1, 2, 3, 4}
   sage: [(r.tmin,r.emin,r.smin,v) for (r,v) in G.split_element((1,2,4)).items()]
   [(1, 0, 3, [1, 2]), (2, 1, 1, [4])]
   sage: G.degree((4,))
   region(e = 1, s = 1, t = 2)

A :meth:`YacopGrading` can be suspended in `(i,e,s)`-space::

   sage: H = suspension(G,t=7,e=3) ; H
   suspension (7,3,0) of G
   sage: H.degree((4,))
   region(e = 4, s = 1, t = 9)
   sage: H.bbox()
   region(3 <= e <= 10, 1 <= s <= 3, 7 <= t <= 9)
   sage: suspension(H,t=-2,s=5)
   suspension (5,3,5) of G
   sage: suspension(H,t=-7,e=-3) is G
   True

Truncations work in the same way::

   sage: L = truncation(G,tmin=1,emax=10) ; L
   truncation to region(-Infinity < e <= 10, 1 <= t < +Infinity) of G
   sage: L.bbox()
   region(0 <= e <= 7, 1 <= s <= 3, 1 <= t <= 2)
   sage: L.degree((4,))
   region(e = 1, s = 1, t = 2)
   sage: L.basis()
   {1, 2, 3, 4}
   sage: K = truncation(L,tmax=1) ; K
   truncation to region(-Infinity < e <= 10, t = 1) of G
   sage: K.basis()
   {1, 2, 3}

Suspensions and truncations interact nicely::

   sage: suspension(truncation(G,tmax=7,s=4),s=-2)
   suspension (0,0,-2) of truncation to region(s = 4, -Infinity < t <= 7) of G
   sage: truncation(suspension(G,t=3,s=2),tmin=2,emax=5)
   suspension (3,0,2) of truncation to region(-Infinity < e <= 5, -1 <= t < +Infinity) of G
   sage: suspension(truncation(G,emax=5,tmin=-1),t=3,s=2) is truncation(suspension(G,t=3,s=2),tmin=2,emax=5)
   True


CARTESIAN PRODUCTS::

   sage: dct = []
   sage: dct.append((region(t=1,e=0,s=3),(7)))
   sage: dct.append((region(t=2,e=1,s=1),(8,9)))
   sage: dct.append((region(t=-1,e=4,s=1),(10,11)))
   sage: H = YacopGradingFromDict(dct) ; H.__custom_name = "H"
   sage: T = cartesian_product([G,H]) ; T
   G (+) H
   sage: G.bbox()
   region(0 <= e <= 7, 1 <= s <= 3, 0 <= t <= 2)
   sage: H.bbox()
   region(0 <= e <= 4, 1 <= s <= 3, -1 <= t <= 2)
   sage: T.bbox()
   region(0 <= e <= 7, 1 <= s <= 3, -1 <= t <= 2)
   sage: G.basis(region(t=2,e=1,s=1))
   {4}
   sage: H.basis(region(t=2,e=1,s=1))
   {8, 9}
   sage: T.basis(region(t=2,e=1,s=1))
   {4, 8, 9}

"""
# *****************************************************************************
#  Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
# ******************************************************************************

from sage.misc.classcall_metaclass import ClasscallMetaclass
from sage.rings.infinity import Infinity
from sage.categories.category import Category
from sage.categories.category_singleton import Category_singleton
from sage.categories.enumerated_sets import EnumeratedSets
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.categories.infinite_enumerated_sets import InfiniteEnumeratedSets
from sage.misc.cachefunc import cached_method
from sage.misc.classcall_metaclass import ClasscallMetaclass
from sage.misc.abstract_method import abstract_method
from sage.misc.lazy_attribute import lazy_attribute
from sage.structure.category_object import CategoryObject
from sage.structure.parent import Parent
from sage.sets.integer_range import IntegerRange
from sage.sets.family import Family
from sage.sets.disjoint_union_enumerated_sets import DisjointUnionEnumeratedSets
from sage.sets.finite_enumerated_set import FiniteEnumeratedSet
from sage.rings.integer import Integer
from yacop.utils.region import region
from yacop.categories import YacopObjects
from yacop.categories.functors import suspension, SuspendedObjectsCategory
from yacop.categories.functors import truncation, TruncatedObjectsCategory
from yacop.categories.functors import cartesian_product, CartesianProductsCategory
from yacop.categories.functors import tensor, TensorProductsCategory
from sage.structure.unique_representation import (
    CachedRepresentation,
    UniqueRepresentation,
)
from sage.structure.sage_object import SageObject
from sage.combinat.free_module import CombinatorialFreeModule
import operator
from yacop.utils.suspenders import Suspender
from yacop.utils.set_of_elements import SetOfMonomials, SetOfElements
from yacop.utils.walker import Walker

"""
Fix pickling doc tests::

    sage: import __main__
    sage: from yacop.utils.gradings import Gradings
    sage: __main__.Gradings = Gradings
"""


class Gradings(Category_singleton):
    """
    A category of gradings, where a grading represents an abstract view
    on some other object.

    EXAMPLES::

        sage: from yacop.utils.gradings import Gradings, SampleGrading
        sage: Gradings()
        Category of gradings
        sage: Gradings().super_categories()
        [Category of yacop graded objects]

        sage: G=SampleGrading(IntegerRange(1,19),7) ; G
        mod 7 decomposition of the range {1, ..., 18}
        sage: G.basis((3,5))
        [3, 5, 10, 12, 17]
        sage: G.bbox()
        {0, ..., 6}
        sage: sorted((i,sorted(j)) for (i,j) in G.split_element((6,13,9)).items())
        [(2, [9]), (6, [6, 13])]
        sage: G.degree((3,10))
        3

        sage: from yacop import *
        sage: H=suspension(G,offset=2) ; H
        suspension with offset 2 of mod 7 decomposition of the range {1, ..., 18}
        sage: suspension(suspension(G,offset=5),offset=8)
        suspension with offset 13 of mod 7 decomposition of the range {1, ..., 18}
        sage: H is suspension(H,offset=0)
        True
        sage: G is suspension(G,offset=0)
        True
        sage: G is suspension(H,offset=-2)
        True
        sage: H.bbox()
        {2, ..., 8}
        sage: H.basis((6,))
        [4, 11, 18]
        sage: H.degree((16,))
        4

    TESTS::

        sage: TestSuite(Gradings()).run()
    """

    @cached_method
    def super_categories(self):
        """
        EXAMPLES::

            sage: from yacop.utils.gradings import Gradings
            sage: Gradings().super_categories()
            [Category of yacop objects]
        """
        return [
            YacopObjects(),
        ]

    class ParentMethods:
        @abstract_method(optional=False)
        def basis(self, region=None):
            """
            return a basis for the region
            """

        @abstract_method(optional=False)
        def bbox(self):
            """
            return a bounding box
            """

        @abstract_method(optional=False)
        def split_element(self, elem):
            """
            split the element `e` into homogeneous pieces `e = sum_i e_i`
            and return the dictionary { i : e_i }
            """

        def nontrivial_degrees(self, region=None):
            """
            return the degrees in which ``self.basis(region)`` is concentrated
            """
            return self._nontrivial_degrees_from_basis(region)

        def _nontrivial_degrees_from_basis(self, region):
            """
            default implementation of ``nontrivial_degrees``
            """

            class nontrivdeg_walker(Walker):
                def __init__(self, grading):
                    Walker.__init__(self)
                    self.gr = grading

                def __iter__(self):
                    self.basis_iter = self.gr.basis(region).__iter__()
                    self.dct = dict()
                    self.xdegs = []
                    return self

                def __next__(self):
                    if len(self.xdegs) > 0:
                        return self.xdegs.pop()
                    # the next line will eventually raise our StopIteration
                    x = next(self.basis_iter)
                    for k in list(self.gr.split_element(x).keys()):
                        if k not in self.dct:
                            self.dct[k] = 1
                            self.xdegs.append(k)
                    return next(self)

                def _repr_(self):
                    return "nontrivial degree walker of %s" % self.gr

            return Family(nontrivdeg_walker(self), lambda x: x, lazy=True)

        def degree(self, elem):
            degs = list(self.split_element(elem).keys())
            if len(degs) == 0:
                raise ValueError("degree of zero is undefined")
            if len(degs) == 1:
                return degs[0]
            raise ValueError("element is not homogeneous")

        def _format_(self, other):
            return "%s" % other

        def _format_term(self, elem):
            return self._format_(elem)

        def _latex_term(self, elem):
            from sage.misc.latex import latex

            return elem

        @abstract_method(optional=False)
        def suspenders(self):
            """
            Group of suspenders that act on this grading.

            EXAMPLE::
                sage: from yacop.modules.projective_spaces import RealProjectiveSpace
                sage: M = RealProjectiveSpace()
                sage: S = M.grading().suspenders() ; S
                Group of suspenders for graded modules over the Steenrod algebra
                sage: from yacop.utils.gradings import Suspender
                sage: S is Suspender
                True
            """
            pass

        @abstract_method(optional=True)
        def SubquotientGrading(subquotient):
            """
            Create a grading for a subquotient.
            """

        def tensor(*gradings):
            return gradings[0].__class__.TensorProduct(
                gradings, category=tensor.category_from_parents(gradings)
            )

    class ElementMethods:
        pass

    class SuspendedObjects(SuspendedObjectsCategory):
        def extra_super_categories(self):
            return [self.base_category()]

    class TruncatedObjects(TruncatedObjectsCategory):
        def extra_super_categories(self):
            return [self.base_category()]

    class CartesianProduct(CartesianProductsCategory):
        def extra_super_categories(self):
            return [self.base_category()]

    class TensorProducts(TensorProductsCategory):
        def extra_super_categories(self):
            return [self.base_category()]


class SampleGrading(Parent, metaclass=ClasscallMetaclass):
    def __init__(self, range, modulus):
        self._range = range
        self._mod = modulus
        CategoryObject.__init__(self, category=Gradings())

    def _format_(self, other):
        return self._repr_()

    def _repr_(self):
        return "mod %d decomposition of the range %s" % (self._mod, self._range)

    def bbox(self):
        return IntegerRange(Integer(0), Integer(self._mod))

    def split_element(self, elements):
        from sage.rings.integer_ring import ZZ

        if elements in ZZ:
            elements = (elements,)
        m = self._mod
        ans = dict()
        for e in elements:
            try:
                x = ans[e % m]
            except:
                x = []
            x.append(e)
            ans[e % m] = x
        return ans

    def basis(self, reg):
        return [i for i in self._range if (i % self._mod) in reg]

    def suspenders(self):
        # from sage.rings import Integers
        return Integers()


class SampleGrading_SuspendedObjects(SampleGrading):
    @staticmethod
    def __classcall_private__(cls, other, offset):
        if offset == 0:
            return other
        return type.__call__(cls, other, offset)

    def __init__(self, other, offset):
        self._other = other
        self._off = offset
        SampleGrading.__init__(self, other._range, other._mod)

    def _format_(self, other):
        return "suspension with offset %d of %s" % (self._off, self._other)

    def _repr_(self):
        return "suspension with offset %d of %s" % (self._off, self._other)

    def bbox(self):
        r = self._other.bbox()
        f, l = r.first(), r.last()
        o = self._off
        return IntegerRange(Integer(f + o), Integer(l + 1 + o))

    def basis(self, reg=region()):
        oreg = [u - self._off for u in reg]
        return self._other.basis(oreg)

    def split_element(self, lst):
        l = [
            (k + self._off, v)
            for (k, v) in list(self._other.split_element(lst).items())
        ]
        return dict(l)


class SampleGrading_SuspendedObjects2(SampleGrading_SuspendedObjects):
    @staticmethod
    def __classcall_private__(cls, other, offset):
        if offset == 0:
            return other
        return SampleGrading_SuspendedObjects(other._other, other._off + offset)


SampleGrading.SuspendedObjects = SampleGrading_SuspendedObjects
SampleGrading_SuspendedObjects.SuspendedObjects = SampleGrading_SuspendedObjects2


class YacopGrading(Parent):
    """
    A base class for gradings by regions as per :meth: `yacop.utils.region`.
    """

    def __init__(self, suspension_symbol="S", suspension_symbol_latex="\\sigma"):
        Parent.__init__(self, category=Gradings())
        self._susp_sym = suspension_symbol
        self._susp_sym_latex = suspension_symbol_latex

    def suspenders(self):
        return Suspender().parent()

    def basis_coefficients(self, elem, region=None):
        """
        decompose a homogeneous element of a module in terms of the graded basis.
        """
        # This default implementation assumes that the
        # elements of graded_basis() are monomials.
        ans = []
        gb = self.basis(region)
        try:
            assert gb.is_finite()
        except AttributeError:
            try:
                assert gb.cardinality() < Infinity
            except NotImplementedError:
                pass
        for b in gb:
            ((k, v),) = list(b.monomial_coefficients().items())
            ans.append(elem[k] / v)
        return ans


class SubquotientGrading(YacopGrading):
    """
    Grading of a subquotient of a yacop graded module.
    """

    def __init__(self, subquotient):
        self._sq = subquotient
        self._am = subquotient.ambient()
        # ogr = self._am.grading()
        YacopGrading.__init__(self)

    def _repr_(self):
        return "subquotient grading of %s" % self._sq

    def basis(self, region=None):
        # this assumes a _basis_walker method in the subquotient object
        wk = self._sq._basis_walker(region)
        if self._am.graded_basis(region).cardinality() < Infinity:
            cat = FiniteEnumeratedSets()
        else:
            cat = InfiniteEnumeratedSets()
        res = Family(wk, lambda i: i, lazy=True)
        res._refine_category_(cat)
        return res

    def bbox(self):
        return self._am.grading().bbox()

    def nontrivial_degrees(self, region=None):
        class sqg_walker(Walker):
            def __init__(self, grading, region):
                Walker.__init__(self)
                self.gr = grading
                self.amg = grading._am.grading()
                self.reg = region

            def __iter__(self):
                self.degiter = self.amg.nontrivial_degrees(self.reg).__iter__()
                return self

            def __next__(self):
                deg = next(self.degiter)
                b = self.gr.basis(deg)
                # len(b) might not be implemented
                try:
                    x = next(b.__iter__())
                    return deg
                except StopIteration:
                    pass
                return next(self)

            def _repr_(self):
                return "nontrivial degree walker of %s" % self.gr

        return Family(sqg_walker(self, region), lambda u: u, lazy=True)

    def split_element(self, elem):
        X = self._am
        Y = self._sq
        ans = dict()
        for (key, val) in X.grading().split_element(Y.lift(elem)).items():
            ans[key] = Y.retract(val)
        return ans


YacopGrading.SubquotientGrading = SubquotientGrading


class YacopGrading_SuspendedObjects(YacopGrading, CachedRepresentation):
    @staticmethod
    def __classcall__(cls, other, t=0, e=0, s=0):
        if t == 0 and e == 0 and s == 0:
            return other
        return super(YacopGrading_SuspendedObjects, cls).__classcall__(
            cls, other, t=t, e=e, s=s
        )

    def __init__(self, other, **kwargs):
        YacopGrading.__init__(self)
        self._other = other
        self._kwargs = kwargs
        self._off = region(**kwargs)
        self._neg = self._off.negative()

    def _format_(self, other):
        return "suspension (%d,%d,%d) of %s" % (
            self._off.val("t", 0),
            self._off.val("e", 0),
            self._off.val("s", 0),
            other,
        )

    def _format_term(self, other):
        x = Suspender(t=self._off.tmin, e=self._off.emin, s=self._off.smin)
        if x == Suspender():
            return other
        return "(%s)*%s" % (other, x)

    def _latex_term(self, other):
        x = Suspender(t=self._off.tmin, e=self._off.emin, s=self._off.smin)
        if x == Suspender():
            return other
        return "\\left( %s \\right)%s" % (other, x._latex_())

    def _repr_(self):
        return self._format_(self._other)

    def bbox(self):
        return self._other.bbox() + self._off

    def basis(self, reg=None):
        if reg is None:
            reg = region()
        b = self._other.basis(reg + self._neg)
        if b.cardinality() == 0:
            return FiniteEnumeratedSet(())
        x = next(iter(b))
        dom = suspension(x.parent(), **self._kwargs)
        mapfunc = lambda x: x.suspend(**self._kwargs)
        unmapfunc = lambda x: x.suspend(t=self._neg.t, e=self._neg.e, s=self._neg.s)
        return SetOfElements(dom, b, b.cardinality(), mapfunc, unmapfunc)

    def split_element(self, lst):
        l = [
            (k + self._off, v)
            for (k, v) in list(self._other.split_element(lst).items())
        ]
        try:
            # suspend the elements - for some gradings this is not necessary/possible
            l = [(k, v.suspend(**self._kwargs)) for (k, v) in l]
        except:
            pass
        return dict(l)


YacopGrading.SuspendedObjects = YacopGrading_SuspendedObjects


class YacopGrading_SuspendedObjects2(YacopGrading_SuspendedObjects):
    @staticmethod
    def __classcall_private__(cls, other, **kwargs):
        dct = {"i": 0, "e": 0, "s": 0}
        dct.update(kwargs)
        reg = region(**dct)
        if region(t=0, e=0, s=0).contains(reg):
            return other
        noff = other._off + reg
        return YacopGrading_SuspendedObjects(
            other._other, t=noff.tmin, e=noff.emin, s=noff.smin
        )


YacopGrading_SuspendedObjects.SuspendedObjects = YacopGrading_SuspendedObjects2

###############################################################################################
###############################################################################################
###############################################################################################
###############################################################################################


class YacopGrading_TruncatedObjects(YacopGrading, CachedRepresentation):
    @staticmethod
    def __classcall__(cls, other, **kwargs):
        reg = region(**kwargs)
        if reg.is_full():
            return other
        return super(YacopGrading_TruncatedObjects, cls).__classcall__(
            cls, other, **reg.as_dict()
        )

    def __init__(self, other, **kwargs):
        YacopGrading.__init__(self)
        self._other = other
        self._off = region(**kwargs)

    def _format_(self, other):
        return "truncation to %s of %s" % (self._off, other)

    def _format_term(self, other):
        return other

    def _repr_(self):
        return self._format_(self._other)

    def bbox(self):
        return self._other.bbox().intersect(self._off)

    def basis(self, reg=None):
        if reg is None:
            reg = region()
        return self._other.basis(reg.intersect(self._off))

    def split_element(self, lst):
        return self._other.split_element(lst)


YacopGrading.TruncatedObjects = YacopGrading_TruncatedObjects


class YacopGrading_TruncatedObjects2(YacopGrading_TruncatedObjects):
    @staticmethod
    def __classcall_private__(cls, other, **kwargs):
        reg = region(**kwargs)
        if reg.is_full():
            return other
        noff = other._off.intersect(reg)
        return YacopGrading_TruncatedObjects(other._other, **(noff.as_dict()))


YacopGrading_TruncatedObjects.TruncatedObjects = YacopGrading_TruncatedObjects2


class YacopGrading_TruncOfSuspObjects(YacopGrading_SuspendedObjects):
    """
    Truncation of a suspension
    """

    @staticmethod
    def __classcall_private__(cls, other, **kwargs):
        reg = region(**kwargs)
        if reg.is_full():
            return other
        shft = other._off
        reg = reg + shft.negative()
        return suspension(
            truncation(other._other, **(reg.as_dict())),
            t=shft.tmin,
            e=shft.emin,
            s=shft.smin,
        )


YacopGrading_SuspendedObjects.TruncatedObjects = YacopGrading_TruncOfSuspObjects

###############################################################################################
###############################################################################################
###############################################################################################
###############################################################################################


class YacopGrading_CartesianProduct(YacopGrading):
    def __init__(self, gradings, **options):
        YacopGrading.__init__(self)
        self._summands = gradings

    def basis(self, region=None):
        if hasattr(self, "_domain"):
            # hack: we're grading a Steenrod algebra module
            gb = []
            for idx in range(0, len(self._summands)):

                def mkfam(emb, xx):
                    return xx.map(lambda u: emb(u))

                x = self._summands[idx].basis(region)
                gb.append(mkfam(self._domain.summand_embedding(idx), x))
            if all(fam.cardinality() < Infinity for fam in gb):
                category = FiniteEnumeratedSets()
            else:
                category = EnumeratedSets()
            return DisjointUnionEnumeratedSets(gb, keepkey=False, category=category)

        # this is probably a sample grading...
        return set.union(*[x.basis(region) for x in self._summands])

    def bbox(self):
        return region.span(*[g.bbox() for g in self._summands])

    def split_element(self, elem):
        M = elem.parent()
        res = {}
        for i in range(0, len(self._summands)):
            g = self._summands[i]
            p = elem.cartesian_projection(i)
            for k, v in g.split_element(p).items():
                v2 = M.summand_embedding(i)(v)
                try:
                    res[k] += v2
                except KeyError:
                    res[k] = v2
        return res

    def _format_(self, other):
        l = [
            self._summands[i]._format_(other.summand_embedding(i).domain())
            for i in (0, len(self._summands))
        ]
        from sage.categories.cartesian_product import cartesian_product

        return cartesian_product.symbol.join(l)

    def _repr_(self):
        from sage.categories.cartesian_product import cartesian_product

        return cartesian_product.symbol.join(["%s" % g for g in self._summands])

    class ElementMethods:
        pass


YacopGrading.CartesianProduct = YacopGrading_CartesianProduct


class YacopGrading_TensorProduct(YacopGrading):

    """
    The grading that is used by a tensor product of Steenrod algebra modules.

    TESTS::

        sage: from yacop.modules.classifying_spaces import BZp
        sage: M = BZp(3) ; M.rename("M")
        sage: N = tensor((M,)) ; N
        M
        sage: N.category()
        Category of tensor products of yacop left module algebras over mod 3 Steenrod algebra, milnor basis
        sage: for dim in (-5,..,10):
        ....:   assert( M.dimension(t=dim) == N.dimension(t=dim) )
        ....:   assert( M.dimension(t=dim,e=-1) == N.dimension(t=dim,e=-1) )
        sage: P = tensor((M,M)) ; P
        M # M
        sage: P.category() is N.category()
        True
        sage: P.bbox()
        region(-2 <= e <= 0, s = 0, 0 <= t < +Infinity)
        sage: B = P.graded_basis(tmax=4,e=-2) ; B
        basis in region(e = -2, s = 0, 0 <= t <= 4) of M # M
        sage: sorted(B)
        [y # y, y # y*x, y*x # y]
        sage: [P.dimension(t=dim) for dim in (-1,..,10)]
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
        sage: from yacop.utils.suspenders import Suspender
        sage: S = Suspender(t=1)
        sage: P2 = tensor((S*M,S**(-3)*M)) ; P2
        suspension (1,0,0) of M # suspension (-3,0,0) of M
        sage: all(P.dimension(t=dim+2) == P2.dimension(t=dim) for dim in (-5,..,15))
        True
        sage: Q = tensor((N,P)) ; Q
        M # M # M
        sage: N.category()
        Category of tensor products of yacop left module algebras over mod 3 Steenrod algebra, milnor basis
        sage: TestSuite(M).run() # long time
        sage: TestSuite(N).run() # long time
        sage: TestSuite(P).run() # long time
        sage: TestSuite(Q).run() # long time

        sage: M.inject_variables()
        Defining y, x
        sage: S = Suspender(t=1)
        sage: tensor((x,x)).parent() is P
        True
        sage: tensor((x*S**2,y*S))
        (x)*S(2,0,0) # (y)*S(1,0,0)

    Some tests with modules that are bounded above::

        sage: from yacop.modules.dual_steenrod_algebra import DualSteenrodAlgebra
        sage: D = DualSteenrodAlgebra(3) ; D.bbox()
        region(-Infinity < e <= 0, s = 0, -Infinity < t <= 0)
        sage: DDS = tensor((S**(-3)*D,S**(-1)*D)) ; DDS.bbox()
        region(-Infinity < e <= 0, s = 0, -Infinity < t <= -4)
        sage: TestSuite(DDS).run() # long time
        sage: DD = tensor((D,D))
        sage: for dim in (-5,..,1):
        ....:    print (". %3d :"%dim, sorted(iter(DD.graded_basis(t=dim))))
        .  -5 : [1 # tau[1], 1 # tau[0]*xi[1], tau[1] # 1, xi[1] # tau[0], tau[0] # xi[1], tau[0]*xi[1] # 1]
        .  -4 : [1 # xi[1], xi[1] # 1]
        .  -3 : []
        .  -2 : [tau[0] # tau[0]]
        .  -1 : [1 # tau[0], tau[0] # 1]
        .   0 : [1 # 1]
        .   1 : []
        sage: # TODO: here we have to use "iter" because ``DD.graded_basis()``
        sage: # does currently not realize that the basis is finite:
        sage: list(DD.graded_basis(t=-10))
        Traceback (most recent call last):
        ...
        NotImplementedError: infinite ...

    The factors of a tensor product should all be bounded below or all be bounded above, unless
    you know what you are doing::

        sage: tensor((DualSteenrodAlgebra(3),BZp(3)))
        WARNING: tensor product not locally finite in the t-direction
        ...
    """

    def __init__(self, gradings, **options):
        YacopGrading.__init__(self)
        self._factors = gradings
        self._bboxes = [u.bbox() for u in gradings]
        bxs = self._bboxes

        # rewrite M1 # ... # Mn as
        #    S^totoff ( S^(i1)M1 # ... # S^(in)Mn )
        # with connected or coconnected factors S^(ik) M_k

        sgns, offs, totoff = [], [], []
        for var in ("t", "e", "s"):
            if all(g.min(var) > -Infinity for g in bxs):
                tsgn, toffs = +1, [g.min(var) for g in bxs]
            elif all(g.max(var) < +Infinity for g in bxs):
                tsgn, toffs = -1, [g.max(var) for g in bxs]
            else:
                # need SmashResolution ( dual-steenrod-algebra * minimal resolution ) for the psi-map
                print(
                    "WARNING: tensor product not locally finite in the %s-direction"
                    % var
                )
                tsgn, toffs = 0, [0 for g in bxs]  # not sure if this is a good idea ...
            sgns.append(tsgn)
            offs.append(toffs)
            totoff.append(-sum(toffs))
        self._signs = sgns
        self._endpoints = offs
        t, e, s = totoff
        self._totaloff = region(t=t, e=e, s=s)

    @lazy_attribute
    def _modules(self):
        return self._domain._sets

    @lazy_attribute
    def _tc(self):
        return self._domain.tensor_constructor(self._modules)

    def _tdc(self, *args):
        print(self._modules, args)
        # return args
        return self._domain.tensor_constructor(self._modules)(*args)

    def __degree_walker_tc(self, idx, elems, reg):
        for x in self.__degree_walker(idx, elems, reg):
            yield self._tc(*x)

    def __degree_walker(self, idx, elems, reg):
        r"""
        An iterator for the basis of a tensor product.

        INPUT:

        - ``idx`` - iterate through basis of ``M_0 # ... # M_idx``
        - ``elems`` - elements of ``M_(idx+1) # ... # M_n`` that have already been chosen
        - ``reg`` - region to iterate through
        """
        assert idx >= 0
        tmax, emax, smax = reg.tmax, reg.emax, reg.smax
        if tmax < 0 or emax < 0 or smax < 0:
            return
        toff, eoff, soff = [u[idx] for u in self._endpoints]
        tsgn, esgn, ssgn = self._signs
        gr = self._factors[idx]
        if idx == 0:
            # this is the last tensor factor
            r2 = reg.var_mult({"t": tsgn, "e": esgn, "s": ssgn})
            r2 = r2 + region(t=toff, e=eoff, s=soff)
            # print "reg=",reg,"r2=",r2
            for elem in gr.basis(r2):
                yield [
                    elem,
                ] + elems
        else:
            # this is not the last tensor factor
            regmax = region(tmax=tmax, emax=emax, smax=smax)
            r2 = regmax.var_mult({"t": tsgn, "e": esgn, "s": ssgn})
            r2 = r2 + region(t=toff, e=eoff, s=soff)
            for deg in gr.nontrivial_degrees(r2):
                dg2 = deg + region(t=-toff, e=-eoff, s=-soff)
                dg2 = dg2.var_mult({"t": -tsgn, "e": -esgn, "s": -ssgn})
                regred = reg + dg2
                for elem in gr.basis(deg):
                    for x in self.__degree_walker(
                        idx - 1,
                        [
                            elem,
                        ]
                        + elems,
                        regred,
                    ):
                        yield x

    def basis(self, reg=None):
        from sage.sets.set import Set

        assert hasattr(self, "_domain")

        from functools import partial
        from sage.sets.set_from_iterator import EnumeratedSetFromIterator

        if reg is None:
            reg = region()
        reg = reg.intersect(self.bbox())
        reg2 = (reg + self._totaloff).var_mult(
            dict(list(zip(("t", "e", "s"), self._signs)))
        )
        iterfunc = partial(
            self.__degree_walker_tc, idx=len(self._factors) - 1, elems=[], reg=reg2
        )
        sz = 0
        for var in ("t", "e", "s"):
            ma, mi = reg.max(var), reg.min(var)
            if mi > ma:
                return Set(())
            sz += ma - mi
        category = (
            FiniteEnumeratedSets() if sz < +Infinity else InfiniteEnumeratedSets()
        )
        return EnumeratedSetFromIterator(
            iterfunc,
            category=category,
            cache=False,
            name="basis in %s of %s" % (reg, self._domain),
        )

    def bbox(self):
        ans = region(t=0, e=0, s=0)
        for bx in [g.bbox() for g in self._factors]:
            ans = ans + bx
        return ans

    def __degree_of_key(self, key):
        ans = region(t=0, s=0, e=0)
        for (k, M) in zip(key, self._modules):
            ans = ans + M.monomial(k).degree()
        return ans

    def split_element(self, elem):
        res = {}
        for m, c in elem:
            deg = self.__degree_of_key(m)
            x = self._domain._from_dict({m: c})
            try:
                res[deg] += x
            except KeyError:
                res[deg] = x
        return res

    def _format_(self, other):
        l = [g._format_(M) for (g, M) in zip(self._factors, other._sets)]
        from sage.categories.tensor import tensor

        return tensor.symbol.join(l)

    def _repr_(self):
        from sage.categories.tensor import tensor

        return tensor.symbol.join(["%s" % g for g in self._factors])

    class ElementMethods:
        pass


YacopGrading.TensorProduct = YacopGrading_TensorProduct

###############################################################################################
###############################################################################################
###############################################################################################
###############################################################################################


class YacopGradingFromDict(YacopGrading):
    """
    A grading defined by a dictionary { point : set of objects }
    """

    @staticmethod
    def __classcall_private__(cls, dct):
        return super(YacopGradingFromDict, cls).__classcall__(cls, tuple(dct))

    def __init__(self, tple):
        YacopGrading.__init__(self)
        self._dct = {}
        for k, v in tple:
            self._dct[k] = v
        self._bbox = region.span(*(list(self._dct.keys())))

    def _repr_(self):
        return "dictionary grading %s" % (self._dct)

    def bbox(self):
        return self._bbox

    def basis(self, reg=region()):
        g = [set(v) for (k, v) in list(self._dct.items()) if reg.contains(k)]
        if len(g) > 0:
            return set.union(*g)
        return set()

    def split_element(self, lst):
        res = {}
        for (k, v) in list(self._dct.items()):
            for l in lst:
                if l in v:
                    try:
                        val = res[k]
                    except KeyError:
                        res[k] = val = []
                    val.append(l)
        return res


def TestGrading(name, dict):
    X = YacopGradingFromDict(dict)
    X.rename(name)
    return X


# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

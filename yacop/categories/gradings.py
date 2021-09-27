r"""
Yacop category of gradings

"""
# *****************************************************************************
#  Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
# ******************************************************************************

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
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.sage_object import SageObject
from sage.combinat.free_module import CombinatorialFreeModule
import operator
from yacop.utils.suspenders import Suspender
from yacop.utils.set_of_elements import SetOfMonomials, SetOfElements
from yacop.utils.walker import Walker

"""
Fix pickling doc tests::

    sage: import __main__
    sage: from yacop.categories.gradings import Gradings
    sage: __main__.Gradings = Gradings
"""


class Gradings(Category_singleton):
    """
    A category of gradings, where a grading represents an abstract view
    on some other object.

    EXAMPLES::

        sage: from yacop.categories.gradings import Gradings, SampleGrading
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

            sage: from yacop.categories.gradings import Gradings
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
                sage: from yacop.categories.gradings import Suspender
                sage: S is Suspender
                True
            """
            pass

        @abstract_method(optional=True)
        def SubquotientGrading(subquotient):
            """
            Create a grading for a subquotient.
            """

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

# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

r"""
Sets with a Yacop grading in (i,e,s)-coordinates.

Fix pickling doc tests::

    sage: import __main__
    sage: from yacop.utils.finite_graded_set import InfiniteGradedSet, FiniteGradedSet
    sage: __main__.InfiniteGradedSet = InfiniteGradedSet
    sage: __main__.FiniteGradedSet = FiniteGradedSet

TESTS::

   sage: F = FiniteGradedSet(range(0,5),tdegree = lambda n:2*n) ; F
   [0, 1, 2, 3, 4]
   sage: F.category()
   Join of Category of finite enumerated sets and Category of yacop graded sets
   sage: TestSuite(F).run()
   sage: F.bbox()
   region(e = 0, s = 0, 0 <= t <= 8)
   sage: 2 in F, 8 in F
   (True, False)
   sage: F.degree(2)
   region(e = 0, s = 0, t = 4)

   sage: G = F.truncate(tmin=3,smin=-5)
   sage: list(G)
   [2, 3, 4]
   sage: G.category()
   Join of Category of finite enumerated sets and Category of yacop graded sets
   sage: TestSuite(G).run()

   sage: H = loads(dumps(F)) ; H
   [0, 1, 2, 3, 4]
   sage: list(H) == list(F)
   True
   sage: for g in H:
   ....:    assert H.degree(g) == F.degree(g)


"""
# *****************************************************************************
#  Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
# ******************************************************************************

from sage.combinat.free_module import CombinatorialFreeModule
from sage.structure.category_object import CategoryObject
from sage.structure.parent import Parent
from sage.categories.category import Category
from sage.categories.sets_cat import Sets
from sage.categories.enumerated_sets import EnumeratedSets
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.categories.infinite_enumerated_sets import InfiniteEnumeratedSets
from sage.rings.infinity import Infinity
from sage.rings.integer_ring import ZZ
from sage.rings.integer import Integer
from sage.misc.classcall_metaclass import ClasscallMetaclass
from yacop.categories import YacopGradedSets
from yacop.utils.region import region
from yacop.utils.gradings import YacopGrading
from sage.structure.sage_object import SageObject
from sage.misc.cachefunc import cached_method
from sage.sets.finite_enumerated_set import FiniteEnumeratedSet
from sage.structure.unique_representation import UniqueRepresentation
from itertools import islice
from sage.misc.abstract_method import abstract_method
from sage.categories.sets_cat import EmptySetError
from sage.rings.integer import Integer


class InfiniteGradedSet(Parent):
    """
    A base class for infinite yacop graded sets.
    """

    def __init__(self, is_finite=False):
        if is_finite is None:
            is_finite = self.cardinality() < Infinity
        cat = FiniteEnumeratedSets() if is_finite else InfiniteEnumeratedSets()
        Parent.__init__(self, category=(cat, YacopGradedSets()))

    @cached_method
    def cardinality(self):
        b = self.bbox()
        tmin, tmax = b.trange
        emin, emax = b.erange
        smin, smax = b.srange
        if (tmax - tmin) + (emax - emin) + (smax - smin) < Infinity:
            return Integer(len(list(iter(self))))
        return Infinity

    def __iter__(self):
        return self._truncate_region(region()).__iter__()

    def len(self):
        c = self.cardinality()
        if c < Infinity:
            return c
        raise ValueError("infinite set has no len")

    def an_element(self):
        x = list(islice(self, 5))
        if len(x) > 0:
            return x.pop()
        raise EmptySetError

    def some_elements(self):
        return list(islice(self, 50))

    def __contains__(self, elem):
        try:
            deg = self.degree(elem)
            return elem in list(self._truncate_region(deg))
        except:
            return False


class FiniteGradedSet(Parent, UniqueRepresentation):
    """
    dummy documentation, replaced below
    """

    @staticmethod
    def __classcall_private__(
        cls,
        elements=None,
        tdegree=None,
        edegree=None,
        sdegree=None,
        tesfunc=None,
        elemlist=None,
    ):
        if elements is None:
            elements = ()
        if elemlist is None:
            if tdegree is None:
                tdegree = lambda n: 0
            if sdegree is None:
                sdegree = lambda n: 0
            if edegree is None:
                edegree = lambda n: 0
            if tesfunc is not None:
                elemlist = []
                for g in elements:
                    x = tesfunc(g)
                    elemlist.append((g, x[0], x[1], x[2]))
            else:
                elemlist = [(g, tdegree(g), edegree(g), sdegree(g)) for g in elements]
        return super(FiniteGradedSet, cls).__classcall__(
            cls, None, elemlist=tuple(elemlist)
        )

    def __init__(
        self,
        elements=None,
        tdegree=None,
        edegree=None,
        sdegree=None,
        tesfunc=None,
        **kwargs
    ):
        """
        Construct a finite yacop graded set from the given elements and degrees.

        EXAMPLE::

            sage: from yacop.utils.finite_graded_set import FiniteGradedSet
            sage: F=FiniteGradedSet((0,1,2),tdegree=lambda i:2*i,sdegree = lambda n:(n&1))
            sage: list(F)
            [0, 1, 2]
            sage: F.degree(1)
            region(e = 0, s = 1, t = 2)
            sage: F.bbox()
            region(e = 0, 0 <= s <= 1, 0 <= t <= 4)

        """
        self._list = kwargs.pop("elemlist")
        self._elems = []
        self._degs = dict()
        self._gb = dict()
        for (el, i, e, s) in self._list:
            self._elems.append(el)
            self._degs[el] = (i, e, s)
            try:
                x = self._gb[(i, e, s)]
            except KeyError:
                x = []
            x.append(el)
            self._gb[(i, e, s)] = x
        # category = (FiniteEnumeratedSets(),YacopGradedObjects())
        category = (FiniteEnumeratedSets(), YacopGradedSets())
        Parent.__init__(self, category=category)

    def _repr_(self):
        return "[%s]" % ", ".join("%s" % u for u in self._elems)

    @cached_method
    def bbox(self, reg=None):
        lst = self._list
        if len(lst) == 0:
            return region(tmax=5, tmin=10)
        tmax = max(x[1] for x in lst)
        emax = max(x[2] for x in lst)
        smax = max(x[3] for x in lst)
        tmin = min(x[1] for x in lst)
        emin = min(x[2] for x in lst)
        smin = min(x[3] for x in lst)
        res = region(tmax=tmax, tmin=tmin, emax=emax, emin=emin, smin=smin, smax=smax)
        if not reg is None:
            res = res.intersect(reg)
        return res

    def _truncate_region(self, reg):
        res = [u[0] for u in self._list if reg.contains(region(t=u[1], e=u[2], s=u[3]))]
        return FiniteGradedSet(
            res, tesfunc=lambda n: [(x.t, x.e, x.s) for x in (self.degree(n),)][0]
        )

    def degree(self, elem):
        i, e, s = self._degs[elem]
        return region(t=i, e=e, s=s)

    def nontrivial_degrees(self, reg):
        if reg is None:
            reg = region()
        ans = []
        for (i, e, s) in list(self._domain._gb.keys()):
            r = region(t=i, e=e, s=s)
            if reg.contains(r):
                ans.append(r)
        return ans

    def __iter__(self):
        return self._elems.__iter__()

    def cardinality(self):
        return Integer(len(self._elems))

    def __len__(self):
        return len(self._elems)

    def an_element(self):
        if len(self._elems) == 0:
            raise EmptySetError
        lst = list(islice(self, 3))
        return lst.pop()

    def some_elements(self):
        return list(islice(self, 5))

    def __contains__(self, x):
        return x in self._elems

    def _element_constructor(self, x):
        if x in self:
            return x
        else:
            raise ValueError("%s not in %s" % (x, self))


FiniteGradedSet.__doc__ = __doc__


# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

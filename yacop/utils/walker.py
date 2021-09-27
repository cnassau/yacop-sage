r"""
Enumerated Sets from Iterables

TESTS::

   sage: from yacop.utils.walker import Walker
   sage: # implement powers of two as an infinite iterator
   sage: class twopowers(Walker):
   ....:      def __init__(this):
   ....:         Walker.__init__(this)
   ....:      def __iter__(this):
   ....:         this.cnt=1
   ....:         return this
   ....:      def __next__(this):
   ....:         ans = this.cnt
   ....:         this.cnt = this.cnt*2
   ....:         return ans
   ....:      def _repr_(this):
   ....:         return "the powers of two"
   ....:      def __call__(this,x):
   ....:         if x in Integers() and 0 == (x&(x-1)):
   ....:            return x
   ....:         raise ValueError
   sage: X = twopowers() ; X
   the powers of two
   sage: from itertools import islice
   sage: list(islice(X,10))
   [1, 2, 4, 8, 16, 32, 64, 128, 256, 512]
   sage: # once more
   sage: list(islice(X,10))
   [1, 2, 4, 8, 16, 32, 64, 128, 256, 512]
   sage: 65536 in X
   True
   sage: 691 in X
   False
   sage: X in X
   False
   sage: X.category()
   Category of enumerated sets
   sage: X in EnumeratedSets()
   True
   sage: TestSuite(X).run()
   Failure in _test_pickling:
   Traceback (most recent call last):
   ....:
   The following tests failed: _test_pickling
   sage: Y = DisjointUnionEnumeratedSets((X,X)) ; Y
   Disjoint union of Family (the powers of two, the powers of two)
   sage: TestSuite(Y).run()
   Failure in _test_pickling:
   Traceback (most recent call last):
   ....:
   The following tests failed: _test_pickling
   sage: # check that we can create a family from X
   sage: Z = Family(X) ; Z
   Family (the powers of two)
   sage: TestSuite(Z).run()

   sage: L = Family(X,lambda i:i) ; L
   Lazy family (<lambda>(i))_{i in the powers of two}
   sage: TestSuite(L).run() # not tested, known issue
   sage: # Sage bug: the following fails if category is not specified
   sage: D=DisjointUnionEnumeratedSets((L,L),category=EnumeratedSets())
   sage: TestSuite(D).run() # not tested, known issue

   sage: L.cardinality()
   +Infinity
   sage: D.cardinality()
   +Infinity

   sage: T = Walker(category=FiniteEnumeratedSets())
   sage: T.category()
   Category of finite enumerated sets

"""
# *****************************************************************************
#  Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
# ******************************************************************************

from sage.structure.category_object import CategoryObject
from sage.structure.parent import Parent
from sage.categories.enumerated_sets import EnumeratedSets
from sage.rings.infinity import Infinity
from sage.rings.integer_ring import ZZ


class Walker(Parent):
    def __init__(self, category=EnumeratedSets()):
        Parent.__init__(self, ZZ, category=category)

    def __len__(self):
        ans = self.cardinality()
        if ans < Infinity:
            return ans
        raise NotImplementedError

    def cardinality(self):
        return Infinity

    def an_element(self):
        from itertools import islice

        lst = list(islice(self, 3))
        return lst.pop()

    def unrank(self, x):
        return self._unrank_from_iterator(x)

    def rank(self, x):
        return self._rank_from_iterator(x)

    def xxlist(self):
        if self.cardinality() < Infinity:
            return [u for u in self]
        raise ValueError("set is potentially infinite")


# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

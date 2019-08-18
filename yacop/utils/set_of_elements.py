r"""
Enumerated Sets of elements of a CombinatorialFreeModule

TESTS::

   sage: from yacop.utils.set_of_elements import SetOfElements, SetOfMonomials
   sage: C = CombinatorialFreeModule(GF(3),Integers()) ; C
   Free module generated by Integer Ring over Finite Field of size 3
   sage: mapfunc = lambda i : C.monomial(i)-C.monomial(i+1)
   sage: def unmapfunc(x):
   ....:    a,b = x.monomial_coefficients()
   ....:    return min(a,b)
   sage: X = SetOfElements(C,NonNegativeIntegers(),Infinity, mapfunc, unmapfunc) ; X
   <a subset of Free module generated by Integer Ring over Finite Field of size 3 indexed by Non negative integers>
   sage: X.category()
   Category of infinite enumerated sets
   sage: TestSuite(X).run()
   pickling of <class '...SetOfElements_with_category'> not implemented
   sage: C.monomial(257) in X
   False
   sage: C.monomial(-76)-C.monomial(-75) in X
   True
   sage: X in X
   False
   sage: Y = SetOfMonomials(C,NonNegativeIntegers(),Infinity) ; Y
   <a subset of Free module generated by Integer Ring over Finite Field of size 3 indexed by Non negative integers>
   sage: TestSuite(Y).run()
   pickling of <class '...SetOfElements_with_category'> not implemented
   sage: class aniterable(object):
   ....:    def __str__(this):
   ....:       return "an iterable"
   ....:    def __iter__(this):
   ....:       this.val = 7
   ....:       return this
   ....:    def next(this):
   ....:       this.val = this.val+1
   ....:       # must give at least 100 hits for _some_elements_from_iterator
   ....:       if this.val > 200:
   ....:          raise NotImplementedError, "don't you see a pattern???"
   ....:       return this.val
   sage: Z = SetOfMonomials(C,aniterable(),Infinity) ; Z
   <a subset of Free module generated by Integer Ring over Finite Field of size 3 indexed by an iterable>
   sage: Z.category()
   Category of infinite enumerated sets
   sage: TestSuite(Z).run()
   pickling of <class '...SetOfElements_with_category'> not implemented
   sage: class myslice(object):
   ....:     def __init__(this,iterable,max):
   ....:        from itertools import islice
   ....:        this.itc = iter(islice(iterable,max))
   ....:        this.max = max
   ....:        this.ito = iterable
   ....:     def __str__(this):
   ....:        return "first %d elements of %s" % (this.max,this.ito)
   ....:     def next(this):
   ....:        return this.itc.next()
   ....:     def __iter__(this):
   ....:        return myslice(this.ito,this.max)
   sage: Z = SetOfMonomials(C,myslice(aniterable(),5),-1) ; Z
   <a subset of Free module generated by Integer Ring over Finite Field of size 3 indexed by first 5 elements of an iterable>

   sage: Z.category()
   Category of finite enumerated sets
   sage: TestSuite(Z).run()
   pickling of <class '...SetOfElements_with_category'> not implemented
   sage: len(Z)
   5
   sage: list(Z)
   [B[8], B[9], B[10], B[11], B[12]]


"""
#*****************************************************************************
#  Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************

from sage.combinat.free_module import CombinatorialFreeModule
from sage.structure.category_object import CategoryObject
from sage.structure.parent import Parent
from sage.categories.enumerated_sets import EnumeratedSets
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.categories.infinite_enumerated_sets import InfiniteEnumeratedSets
from sage.rings.infinity import Infinity
from sage.rings.integer_ring import ZZ
from sage.rings.integer import Integer
from sage.misc.classcall_metaclass import ClasscallMetaclass
import yacop

"""
Fix pickling doc tests::

    sage: import __main__
    sage: from yacop.utils.set_of_elements import SetOfElements
    sage: __main__.SetOfElements = SetOfElements
"""

class SetOfElements(Parent):
   """
   dummy documentation, replaced below
   """

   # we're only setting __metaclass__ to make __doc__ writable
   __metaclass__ =  ClasscallMetaclass

   def __init__(self,ambient,iterable,size,mapfunc,unmapfunc):
      if size < Infinity:
         category=FiniteEnumeratedSets()
      else:
         category=InfiniteEnumeratedSets()
      Parent.__init__(self,ZZ,category=category)
      self.size = size
      self.fmap = mapfunc
      self.funm = unmapfunc
      self.keys = iterable
      self.am = ambient

   def _repr_(self):
      return "<a subset of %s indexed by %s>" % (self.am,self.keys)

   class walker(object):
      def __init__(self,owner):
         self.owner = owner
         self.it = iter(owner.keys)
      def __iter__(self):
         return self.__class__(self.owner)
      def next(self):
         return self.owner.fmap(self.it.next())

   def __iter__(self):
      return SetOfElements.walker(self)

   def cardinality(self):
      if self.size < 0:
         self.size = len(list(iter(self)))
      if self.size == Infinity:
         return Infinity
      return Integer(self.size)

   def __len__(self):
      ans = self.cardinality()
      if ans < Infinity:
         return self.size
      raise AttributeError, "set is infinite"

   def an_element(self):
      from itertools import islice
      lst = list(islice(self,3))
      return lst.pop()

   def some_elements(self):
      # 5 is plenty
      from itertools import islice
      return list(islice(self,5))

   def __contains__(self,x):
      try:
         # the unmap function can throw any kind of error
         # for foreign input
         key = self.funm(x)
         return x == self.fmap(key)
      except:
         return False

   def _test_pickling(self,tester=None,**options):
      print("pickling of %s not implemented" % self.__class__)


SetOfElements.__doc__ = __doc__

def SetOfMonomials(ambient,iterable,size):
   mf = lambda k:ambient.monomial(k)
   def uf(x):
       k, = x.monomial_coefficients()
       return k
   return SetOfElements(ambient,iterable,size,mf,uf)




# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:



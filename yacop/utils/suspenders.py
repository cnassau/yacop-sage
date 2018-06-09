r"""
Suspenders are syntactic sugar for working with suspensions::

   sage: from yacop.modules.classifying_spaces import BZp
   sage: from yacop.utils.suspenders import Suspender
   sage: from yacop.modules.functors import suspension
   sage: S=Suspender(t=3) ; S
   S(3,0,0)
   sage: M=BZp(5) ; M
   mod 5 cohomology of the classifying space of ZZ/5ZZ
   sage: S*M
   suspension (3,0,0) of mod 5 cohomology of the classifying space of ZZ/5ZZ
   sage: M*S is S*M
   True
   sage: S**(-1)*M*S is M
   True
   sage: S**(-1)*M is M*S**(-1)
   True
   sage: S**(-3) == Suspender(t=-9)
   True
   sage: suspension(M,t=0) is M
   True

On elements suspension does the right thing with signs::

   sage: M.inject_variables()
   Defining y, x
   sage: S*x == x*S      # S commutes with the even generator x
   True
   sage: S*y == -y*S     # S anti-commutes with the odd generator y
   True

We suspend from the right, so Steenrod operations commute with suspensions::

   sage: y.suspend(t=3) == y*S
   True
   sage: Q=SteenrodAlgebra(5).Q(2)
   sage: Q*(y.suspend(t=3)) == (Q*y).suspend(t=3)
   True
   sage: Q*y*S
   (x^25)*S(3,0,0)

"""
#*****************************************************************************
#  Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************

from yacop.utils.region import region
from yacop.modules.functors import suspension
from sage.combinat.free_module import CombinatorialFreeModule
from sage.rings.integer_ring import ZZ
from sage.categories.monoids import Monoids
from sage.categories.commutative_additive_monoids import CommutativeAdditiveMonoids
from yacop.modules.categories import YacopGradedObjects
from sage.rings.infinity import Infinity

"""
Fix pickling doc tests::

    sage: import __main__
    sage: from yacop.utils.suspenders import YacopSuspender
    sage: __main__.YacopSuspender = YacopSuspender
"""

class YacopSuspender(CombinatorialFreeModule):
    """
    Implementation of the "suspenders" for yacop graded objects.
    This is just a free abelian group on three generators, corresponding
    to the i,e,s-grading of differential graded Steenrod algebra modules.

    TESTS::

        sage: from yacop.utils.suspenders import Suspender
        sage: Suspender(t=1)
        S(1,0,0)
        sage: Suspender(s=3)
        S(0,0,3)
        sage: Suspender(e=1,s=1)
        S(0,1,1)
        sage: Suspender(1,2,3)
        S(1,2,3)
    """

    def __init__(self):
       CombinatorialFreeModule.__init__(self,ZZ,(0,1,2))

    def _repr_(self):
       return "Group of suspenders for graded modules over the Steenrod algebra"

    def _element_constructor_(self,*args,**kwargs):
        if len(args) == 3:
          try:
             t,e,s = args
             return self._from_dict({0:t,1:e,2:s})
          except:
             ar2 = ["%s" % u for u in args]
             raise ValueError, "suspender not recognized: %s" % ", ".join(ar2)
        try:
          r = region(**kwargs)
          dct = {0:0,1:0,2:0}
          if r.tmin != -Infinity:
              assert(r.tmax == r.tmin)
              dct[0] = r.tmin
          if r.emin != -Infinity:
              assert(r.emax == r.emin)
              dct[1] = r.emin
          if r.smin != -Infinity:
              assert(r.smax == r.smin)
              dct[2] = r.smin
          return self._from_dict(dct)
        except KeyError:
          pass
        if len(args) == 1 and args[0] == 0:
           return self.zero()
        ar2 = ["%s" % x for x in args]
        kw2 = ["%s=%s" % (a,b) for (a,b) in kwargs.iteritems()]
        raise ValueError, "cannot make suspender from %s" % ", ".join(ar2 + kw2)

    def an_element(self):
       return self._element_constructor_(2,0,1)

    class Element(CombinatorialFreeModule.Element):
        def _repr_(self):
            return "S(%d,%d,%d)" % (self[0],self[1],self[2])

        def _latex_(self):
           return "\\Sigma^{%d,%d,%d}" % (self[0],self[1],self[2])

        def _mul_(self,othr):
            return self._add_(othr)

        def __pow__(self,n):
            t,e,s = self[0],self[1],self[2]
            return self.parent()._from_dict({0:n*t,1:n*e,2:n*s})

        def suspension_args(self):
            """
            Arguments to supply to the suspension functor.

            EXAMPLE::

                sage: from yacop.modules.projective_spaces import RealProjectiveSpace
                sage: from yacop.utils.suspenders import Suspender
                sage: from yacop.modules.functors import suspension
                sage: M=RealProjectiveSpace()
                sage: S=Suspender(s=2)
                sage: suspension(M,s=2) is suspension(M,**S.suspension_args())
                True
            """
            return dict([('t',self[0]),('e',self[1]),('s',self[2])])

        def _act_on_(self,othr,self_is_left):
           try:
              dct = self.suspension_args()
              if not self_is_left or (self[0]&1)==0:
                 return othr.suspend(**dct)
              ans = []
              for (deg,elem) in othr.homogeneous_decomposition().iteritems():
                 e = elem.suspend(**dct)
                 tmin,tmax=deg.trange
                 if tmin&1:
                    ans.append(-e)
                 else:
                    ans.append(e)
              return sum(ans)
           except:
              pass
           if othr in YacopGradedObjects():
              return suspension(othr,**self.suspension_args())
           raise ValueError, "do not know how to suspend %s" % othr

YacopSuspender.__doc__ = __doc__

Suspender = YacopSuspender()

r"""
   TESTS::

      sage: from yacop.utils.suspenders import Suspender
      sage: TestSuite(Suspender).run()
"""

# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

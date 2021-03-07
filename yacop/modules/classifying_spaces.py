r"""
Cohomology of classifying spaces as modules over the Steenrod algebra.

AUTHORS: - Christian Nassau (2011-05-13: version 1.0)

Fix picklin::

    sage: import __main__
    sage: from yacop.modules.classifying_spaces import *
    sage: __main__.BZpGeneric = BZpGeneric

=============
Cyclic groups
=============

EXAMPLES AND TESTS:

The construction of these modules is straightforward::

    sage: from yacop.modules.classifying_spaces import BZp
    sage: M = BZp(2) ; M
    mod 2 cohomology of real projective space P^{+Infinity}_{0}
    sage: M = BZp(3) ; M
    mod 3 cohomology of the classifying space of ZZ/3ZZ
    sage: TestSuite(M).run()

    sage: N = BZp(5,varnames=("u","v"))
    sage: N.inject_variables()
    Defining u, v
    sage: # check degrees of the exterior generator u and the polynomial generator v
    sage: u.t,u.e,v.t,v.e
    (1, -1, 2, 0)
    sage: N.bbox() == region(s=0,emin=-1,emax=0,tmin=0,tmax=+Infinity)
    True
    sage: sorted(N.graded_basis(region(tmax=10)))
    [1, u, v, u*v, v^2, u*v^2, v^3, u*v^3, v^4, u*v^4, v^5]
    sage: # test Steenrod algebra action
    sage: A = SteenrodAlgebra(5)
    sage: P,Q = A.P, A.Q
    sage: Q(0)*u == v and Q(1)*u == v**5
    True
    sage: P(1)*u, P(1)*v
    (0, v^5)
    sage: P(1)*P(1)*v**4
    2*v^12

    sage: from yacop.modules.classifying_spaces import BZp
    sage: from yacop.utils.region import region
    sage: P = BZp(3)
    sage: P._manual_test_left_action(region(tmax=20))
    183 non-zero multiplications checked
    sage: P._manual_test_left_conj_action(region(tmax=20))
    207 non-zero multiplications checked


CLASS DOCUMENTATION:
"""

#*****************************************************************************
#       Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#  Distributed under the terms of the GNU General Public License (GPL)
#*****************************************************************************

from yacop.utils.region import region
from yacop.utils.gradings import YacopGrading
from yacop.utils.set_of_elements import SetOfMonomials, SetOfElements
from yacop.modules.module_base import SteenrodModuleBase
from yacop.modules.categories import YacopLeftModuleAlgebras, YacopGradedObjects
from yacop.modules.functors import suspension, SuspendedObjectsCategory
from yacop.modules.functors import truncation, TruncatedObjectsCategory
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
from yacop.utils.bitstuff import binom_modp

r"""

  TESTS::

      sage: from yacop.modules.classifying_spaces import *
      sage: TestSuite(BZp(3,prime=3)).run()

"""

class BZpBasis(InfiniteGradedSet,UniqueRepresentation):

    def __init__(self,module):
        InfiniteGradedSet.__init__(self)

    def bbox(self):
        return region(s=0,emin=-1,emax=0,tmin=0,tmax=Infinity)

    def degree(self,elem):
        return region(s=0,e=-(elem&1),t=elem)

    def _truncate_region(self,reg):
        emin,emax = reg.erange
        smin,smax = reg.srange
        tmin,tmax = reg.trange
        if smax<0 or smin>0 or emax<-1 or emin>0 or tmin>tmax:
            return Set(())
        if tmin<0:
            tmin=0
        if tmax<Infinity:
            tmax=Integer(tmax+1)
        if emax>=0 and emin <=-1:
            return IntegerRange(Integer(tmin),tmax)
        elif emax<0 and emin <=-1:
            return IntegerRange(Integer(tmin|1),tmax,Integer(2))
        else:
            return IntegerRange(Integer(((tmin+1)|1)-1),tmax,Integer(2))

class BZpGeneric(SteenrodModuleBase):
    """
    Cohomology of the classifying space of a cyclic group.

    TESTS::

        sage: from yacop.modules.classifying_spaces import *
        sage: TestSuite(BZp(7)).run()
    """

    @staticmethod
    def __classcall_private__(cls,order,prime=None,varnames=None):
        if varnames is None:
           varnames = ("y","x")
        if prime is None:
           prime = order
        return super(BZpGeneric,cls).__classcall__(cls,order,prime,varnames)

    def __init__(self,order,prime,varnames,category=None):
        """
        mod p cohomology of ZZ/p*ZZ
        """
        assert(prime == order)  # TODO: allow prime != order
        assert is_prime(prime)
        self._n = order
        self._varnames = varnames
        self._prime = prime

        if category is None:
            category=YacopLeftModuleAlgebras(SteenrodAlgebra(prime,generic=True))
        SteenrodModuleBase.__init__(self, BZpBasis(self), category=category)

    def an_element(self):
         """
         Return an element of self. This is used for automatic tests.

         EXAMPLES::

             sage: from yacop.modules.classifying_spaces import *
             sage: N = BZp(5)
             sage: N.an_element()
             y + 3*x^2 + 2*y*x^5
             sage: latex(N.an_element())
             y + 3x^{2} + 2yx^{5}
         """
         dct = []
         for (cf,a,b) in ((2,1,5),(3,0,2),(1,1,0),(5,0,17)):
            dct.append( (self.monomial(a+(b<<1)), cf ) )
         return self.linear_combination( dct )

    def _repr_(self):
        return "mod %d cohomology of the classifying space of ZZ/%dZZ" % (self._prime,self._n)

    def _repr_term_impl(self,elem,numfmt,mulsym):
        yv,xv = self._varnames
        yexp,xexp = elem&1,elem>>1
        if yexp>0: y = "%s%s" % (yv,mulsym)
        else:      y = ""
        if xexp > 1:
           return "%s%s^%s" % (y,xv,numfmt%("%d"%xexp))
        elif xexp < 0:
           return "%s%s^%s" % (y,xv,numfmt%("(%d)"%xexp))
        elif xexp == 1:
           if yexp>0:
              return "%s%s" % (y,xv)
           else:
              return xv
        elif xexp == 0:
           if yexp>0:
              return yv
           else:
              return "1"
        raise ValueError("internal error")

    def _repr_term(self,elem):
       return self._repr_term_impl(elem,"%s","*")

    def _latex_term(self,elem):
       return self._repr_term_impl(elem,"{%s}","")

    def one_basis(self):
        return 0

    def variable_names(self):
        return self._varnames

    def gens(self):
        return [self.monomial(a+2*b) for (a,b) in ((1,0),(0,1))]

    def product_on_basis(self,left,right):
       if left&right&1>0:
          return self.zero()
       return self.monomial(left+right)

    def left_steenrod_action_milnor(self,a,m):
        qexp,Rexp = a
        yexp,xexp = m&1,m>>1
        p = self._prime

        if len(qexp)>1:
           # Q_i Q_j z = 0 for all z
           return self.zero()
        if len(qexp)==1 and yexp==0:
           # Qj(x^k) = 0
           return self.zero()

        # compute P(Rexp)*x^xexp
        sum = 0
        deg = xexp
        ppow = p
        cf = 1
        for i in Rexp:
           sum = sum + i
           if xexp >= 0 and sum > xexp: return self.zero()
           cf *= binom_modp(self._prime,sum,i)
           cf = cf % p
           if 0==cf: return self.zero()
           deg += i*(ppow-1)
           ppow *= p
        rest = xexp-sum
        cf *= binom_modp(self._prime,rest+sum,sum)
        if 0==cf: return self.zero()
        cf = cf % p

        if len(qexp)==0:
           ans = self.monomial(yexp+(deg<<1))
        else:
           # Qi(y) = x^{p^i}
           ans = self.monomial((deg+p**qexp[0])<<1)
        return self.linear_combination(((ans,cf),))

    def left_steenrod_action_milnor_conj(self,a,m):
        """
        TESTS::

            sage: from yacop.modules.classifying_spaces import *
            sage: N = BZp(5) ; N.inject_variables()
            Defining y, x
            sage: A = SteenrodAlgebra(5)
            sage: P = A.P
            sage: for i in range(10):
            ....:     for q in range(3):
            ....:         Q = A.one() if q == 0 else A.Q(q)
            ....:         for r1 in range(10):
            ....:             for r2 in range(3):
            ....:                 op = P(r1,r2)*Q
            ....:                 po = op.antipode()
            ....:                 assert po * (x**i) == op % (x**i)
            ....:                 assert po * (y*x**i) == op % (y*x**i)
        """

        qexp,Rexp = a
        yexp,xexp = m&1,m>>1
        p = self._prime

        cf = 1

        if len(qexp)>1:
            # Q_i Q_j z = 0 for all z
            return self.zero()
        if len(qexp)==1:
            if yexp==0:
                # Qj(x^k) = 0
                return self.zero()
            else:
                # evaluate chi(Q_k)(y*x**i) = -x**(i+p^k) first
                cf = p-1
                yexp = 0
                xexp += p**qexp[0]

        # compute P(Rexp)*x^xexp
        sum = 0
        psum = 0
        deg = xexp
        ppow = p
        for i in Rexp:
           sum = sum + i
           cf *= binom_modp(self._prime,sum,i)
           cf = cf % p
           if 0==cf: return self.zero()
           deg += i*(ppow-1)
           psum += ppow*i
           ppow *= p
        rest = -1-xexp-psum
        cf *= binom_modp(self._prime,rest+sum,sum)
        if 0==cf: return self.zero()
        cf = cf % p

        ans = self.monomial(yexp+(deg<<1))

        return self.linear_combination(((ans,cf),))

def BZp(order,prime=None,varnames=None):
   if order==2:
      from yacop.modules.projective_spaces import RealProjectiveSpace
      return RealProjectiveSpace(prefix=varnames,botexp=0)
   return BZpGeneric(order,prime,varnames)

# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

r"""
The dual of the Steenrod algebra as a Steenrod algebra bimodule algebra.

AUTHORS: - Christian Nassau (2011-05-13: version 1.0)


CLASS DOCUMENTATION:
"""

#*****************************************************************************
#       Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#  Distributed under the terms of the GNU General Public License (GPL)
#*****************************************************************************

from yacop.utils.region import region
from yacop.utils.gradings import YacopGrading
from yacop.utils.set_of_elements import SetOfMonomials, SetOfElements
from yacop.modules.algebras import SteenrodAlgebraBase
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
from yacop.utils.bitstuff import N0
from yacop.modules.xitauring import XiTauRing

"""
  Pickling hack::

    sage: import __main__
    sage: from yacop.modules.dual_steenrod_algebra import *
    sage: __main__.DualSteenrodAlgebra = DualSteenrodAlgebra
"""

class DualSteenrodAlgebra(SteenrodAlgebraBase):

    """
    TESTS::

       sage: from yacop.modules.dual_steenrod_algebra import *
       sage: from yacop import *
       sage: D=DualSteenrodAlgebra(5) ; D
       dual Steenrod algebra at the prime 5
       sage: D is DualSteenrodAlgebra(5)
       True
       sage: D.inject_variables()
       Defining xi, tau
       sage: xi, tau
       (xi-generator family of dual Steenrod algebra at the prime 5, tau-generator family of dual Steenrod algebra at the prime 5)
       sage: xi[2], tau[0]
       (xi[2], tau[0])
       sage: xi[4].parent() is D
       True
       sage: xi[:2]
       [1, xi[1]]
       sage: tau[:2]
       [tau[0], tau[1]]
       sage: xi[4:7]
       [xi[4], xi[5], xi[6]]
       sage: tau[0]*tau[3], tau[2]*tau[1], tau[8]*tau[8]
       (tau[0]*tau[3], 4*tau[1]*tau[2], 0)
       sage: xi[4:]
       Traceback (most recent call last):
       ...
       ValueError: infinite list
       sage: for u in xi[:4]:
       ...      print(u, u.t,u.e,u.s)
       1 0 0 0
       xi[1] -8 0 0
       xi[2] -48 0 0
       xi[3] -248 0 0
       sage: for u in tau[:4]:
       ...      print(u, u.t,u.e,u.s)
       tau[0] -1 -1 0
       tau[1] -9 -1 0
       tau[2] -49 -1 0
       tau[3] -249 -1 0
       sage: D.an_element()
       2 + 3*tau[0]
       sage: D.category()
       Category of Yacop bimodule algebras over mod 5 Steenrod algebra, milnor basis
       sage: TestSuite(D).run()
       sage: D.bbox()
       region(-Infinity < e <= 0, s = 0, -Infinity < t <= 0)
       sage: sorted(D.graded_basis(region(tmin=-30,tmax=-20)))
       [tau[1]*xi[1]**2, xi[1]**3, tau[0]*tau[1]*xi[1]**2, tau[0]*xi[1]**3]

       sage: A = SteenrodAlgebra(5)
       sage: P,Q = A.P,A.Q_exp
       sage: [tau[1]*u for u in [Q(0,1),P(1),P(0)]]
       [1, tau[0], tau[1]]
       sage: [u*tau[1] for u in [Q(1),Q(0,1),P(0)]]
       [xi[1], 1, tau[1]]
       sage: tensor((xi[1],tau[1]))*P(1) == tensor((D.one(),tau[1])) + tensor((xi[1],tau[0]))
       True
       sage: Q(1)*tensor((tau[2],tau[1])) == tensor((xi[2],tau[1])) - tensor((tau[2],xi[1]))
       True
       sage: TestSuite(D.category()).run()

       sage: E = DualSteenrodAlgebra(2) ; E
       dual Steenrod algebra at the prime 2
       sage: TestSuite(E).run()
       sage: E.inject_variables()
       Defining xi
       sage: xi
       xi-generator family of dual Steenrod algebra at the prime 2
       sage: for u in xi[:4]:
       ...      print(u, u.t,u.e,u.s)
       1 0 0 0
       xi[1] -1 0 0
       xi[2] -3 0 0
       xi[3] -7 0 0
       sage: E.an_element()
       xi[1] + xi[1]**2
       sage: E.bbox()
       region(e = 0, s = 0, -Infinity < t <= 0)
       sage: sorted(E.graded_basis(region(t=-7)))
       [xi[3], xi[1]*xi[2]**2, xi[1]**4*xi[2], xi[1]**7]
       sage: TestSuite(E.category()).run()

       sage: F=DualSteenrodAlgebra(2,generic=True) ; F
       generic dual Steenrod algebra at the prime 2
       sage: sorted(F.graded_basis(t=-5))
       [tau[1]*xi[1], tau[0]*xi[1]**2]
       sage: TestSuite(F).run()

       sage: # regression test: make sure submodules are suspendable
       sage: E = DualSteenrodAlgebra(2) ; E.inject_variables()
       Defining xi
       sage: from yacop.modules.morph_module import SubModule
       sage: X = SubModule(E,(xi[2],)) ; X
       submodule of dual Steenrod algebra at the prime 2 generated by (xi[2],)
       sage: suspension(X,t=3) # (not) random, but it prints differently
       suspension (3,0,0) of submodule of dual Steenrod algebra at the prime 2 generated by (xi[2],)
       sage: sorted(X.graded_basis())
       [xi[2], xi[1]**2, 1]

    """

    class Degrees(object):

        def __init__(self, prime, generic):
            self._prime = prime
            self._generic = generic

        def __getitem__(self, idx):
            idx = idx ^ 1
            fac = 2 if self._generic else 1
            if idx & 1:
                # tau_(idx-1)/2
                return (-(2 * self._prime ** ((idx - 1) >> 1) - 1), -1, 0)
            else:
                # xi_(idx/2+1)
                return (-fac * (self._prime ** (1 + (idx >> 1)) - 1), 0, 0)

    def __init__(self, prime, generic='auto', category=None):
        if generic == 'auto':
            generic = False if prime == 2 else True
        self._generic = generic
        degs = DualSteenrodAlgebra.Degrees(prime, generic)
        self._prime = prime
        SteenrodAlgebraBase.__init__(self, XiTauRing(prime,degrees=degs), degs, None,
                                     SteenrodAlgebra(prime, generic=generic),
                                     left_action=True, right_action=True, category=category)

    def octants(self):
        return [(-1, -1, 0)]

    def _is_sorted_by_t_degrees(self):
        return True

    def _max_exponents(self):
        if not self._generic:
            maxodd = 0
        else:
            maxodd = 1
        while True:
            yield maxodd
            yield Infinity

    def _repr_(self):
        gen = "generic " if self._prime == 2 and self._generic else ""
        return "%sdual Steenrod algebra at the prime %d" % (gen, self._prime)

    def _bbox(self):
        if not self._generic:
            return region(tmax=0, emax=0, s=0, tmin=-Infinity, emin=0)
        return region(tmax=0, emax=0, s=0, tmin=-Infinity, emin=-Infinity)

    def variable_names(self):
        if not self._generic:
            return ["xi", ]
        else:
            return ["xi", "tau"]

    class GenFactory(SageObject):

        def __init__(self, par, even):
            self.par = par
            self.even = even

        def _repr_(self):
            v = "xi" if self.even else "tau"
            return "%s-generator family of %s" % (v, self.par)

        def __getitem__(self, val):
            if isinstance(val, slice):
                if val.stop is None:
                    raise ValueError("infinite list")
                start = 0 if val.start is None else val.start
                step = 1 if val.step is None else val.step
                return [self[u] for u in range(start, val.stop, step)]
            idx = val << 1
            if not self.even:
                idx = idx + 1
            else:
                if idx == 0:
                    return self.par.one()
                idx = idx - 2
            idx = idx ^ 1
            return self.par._monomial_gen(idx + 1)

    def _monomial_gen(self, idx, expo=1):
        """
         TESTS::

            sage: from yacop.modules.dual_steenrod_algebra import *
            sage: D=DualSteenrodAlgebra(5)
            sage: for u in range(0,4):
            ...       print(u,D._monomial_gen(u))
            0 1
            1 tau[0]
            2 xi[1]
            3 tau[1]
            sage: D._tau(0)
            tau[0]
            sage: D._xipower(3,5)
            xi[3]**5
            sage: D._xipower(0,2)
            1
        """
        return (
            self.monomial(
                tuple([0 if x < idx else expo for x in range(1, idx + 1)]))
        )

    def _xipower(self, idx, pow=1):
        return self._monomial_gen(idx << 1, pow)

    def _tau(self, idx):
        return self._monomial_gen((idx << 1) + 1)

    def xi(self, idx):
        """
        TESTS::

           sage: from yacop.modules.dual_steenrod_algebra import *
           sage: D=DualSteenrodAlgebra(5)
           sage: D.xi(3)
           xi[3]
           sage: D.xi(0)
           1
        """
        if idx < 0:
            raise ValueError("negative index not allowed")
        return self._xipower(idx)

    def tau(self, idx):
        """
         TESTS::

            sage: from yacop.modules.dual_steenrod_algebra import *
            sage: D=DualSteenrodAlgebra(5)
            sage: D.tau(3)
            tau[3]
            sage: D.tau(-1)
            1
        """
        if not self._generic:
            raise ValueError("tau generator not defined in %s" % self)
        if idx < -1:
            raise ValueError("index < -1 not allowed")
        return self._tau(idx)

    def gens(self):
        ans = [DualSteenrodAlgebra.GenFactory(self, 1), ]
        if self._generic:
            ans.append(DualSteenrodAlgebra.GenFactory(self, 0))
        return ans

    def _coproduct_gen(self, idx):
        """
        TESTS::

           sage: from yacop.modules.dual_steenrod_algebra import *
           sage: D=DualSteenrodAlgebra(5)
           sage: for u in (0,..,6):
           ...      print("%-6s"%D._monomial_gen(u+1), "->", list(D._coproduct_gen(u)))
           tau[0] -> [(tau[0], 1), (1, tau[0])]
           xi[1]  -> [(xi[1], 1), (1, xi[1])]
           tau[1] -> [(tau[1], 1), (xi[1], tau[0]), (1, tau[1])]
           xi[2]  -> [(xi[2], 1), (xi[1]**5, xi[1]), (1, xi[2])]
           tau[2] -> [(tau[2], 1), (xi[2], tau[0]), (xi[1]**5, tau[1]), (1, tau[2])]
           xi[3]  -> [(xi[3], 1), (xi[2]**5, xi[1]), (xi[1]**25, xi[2]), (1, xi[3])]
           tau[3] -> [(tau[3], 1), (xi[3], tau[0]), (xi[2]**5, tau[1]), (xi[1]**25, tau[2]), (1, tau[3])]
        """
        if idx & 1:
            n = (idx + 1) >> 1
            # Delta(xi_n)  = sum xi_{n-i}^{p^i}*xi_i
            ppow = 1
            for i in range(0, n + 1):
                yield self._xipower(n - i, ppow), self._xipower(i)
                ppow = ppow * self._prime
        else:
            n = (idx >> 1)
            # Delta(tau_n) = sum xi_{n-i}^{p^i}*tau_i + tau_n*1
            ppow = 1
            yield self._tau(n), self._xipower(0)
            for i in range(0, n + 1):
                yield self._xipower(n - i, ppow), self._tau(i)
                ppow = ppow * self._prime

    def __toqp(self, elem):
        # hack: elem must be monomial with coefficient 1
        elem, = elem.monomial_coefficients()
        q = 0
        msk = 1
        for idx in elem[::2]:
            if idx:
                q = q | msk
            msk = msk << 1
        return q, elem[1::2]

    def _left_steenrod_coaction_milnor_gen(self, idx, maxQ, maxP):
        """
        TESTS::

            sage: from yacop.modules.dual_steenrod_algebra import DualSteenrodAlgebra
            sage: X=DualSteenrodAlgebra(3) ; X.inject_variables()
            Defining xi, tau
            sage: from yacop.utils.region import region
            sage: print(X._manual_test_left_action(region(tmin=-30,tmax=10),20)) # long time
            2793 multiplications checked
            sage: print(X._manual_test_right_action(region(tmin=-30,tmax=10),20)) # long time
            2793 multiplications checked
            sage: print(X._manual_test_bimod_action(region(tmin=-30,tmax=10),20)) # long time
            2793 multiplications checked
            sage: A=SteenrodAlgebra(3) ; P=A.P
            sage: # this was broken once
            sage: (P(3)*P(1)*(xi[3]*tau[0]*tau[2])) == P(3)*(P(1)*(xi[3]*tau[0]*tau[2]))
            True

        """
        for (ff, sf) in self._coproduct_gen(idx):
            q, p = self.__toqp(sf)
            yield self._coaction_tensor(ff, q, p)

    def _right_steenrod_coaction_milnor_gen(self, idx, maxQ, maxP):
        for (ff, sf) in self._coproduct_gen(idx):
            q, p = self.__toqp(ff)
            yield self._coaction_tensor(sf, q, p)




# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:
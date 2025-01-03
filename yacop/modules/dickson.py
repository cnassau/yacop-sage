r"""
The Dickson-Mui algebras as algebras over the Steenrod algebra.

  THIS FILE IS WORK IN PROGRESS - NOT EVERYTHING IS WORKING (OR EVEN IMPLEMENTED)
  ===============================================================================

Some references:

Masaki Kameko, Mamoru Mimura,
Mui invariants and Milnor operations
https://arxiv.org/abs/0903.4912

Steenrod operations on the modular invariants
Sum Nguyen
Source: Kodai Math. J. Volume 17, Number 3 (1994), 585-595.

http://projecteuclid.org/euclid.kmj/1138040053

AUTHORS: - Christian Nassau (2018)


CLASS DOCUMENTATION:
"""

"""
  Pickling hack::

    sage: import __main__
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
from sage.categories.algebras_with_basis import AlgebrasWithBasis
from sage.categories.cartesian_product import cartesian_product
from sage.sets.integer_range import IntegerRange
from sage.algebras.all import SteenrodAlgebra, Sq
from sage.rings.integer import Integer
from sage.structure.formal_sum import FormalSum, FormalSums
from sage.structure.unique_representation import UniqueRepresentation
from sage.arith.misc import is_prime
from yacop.utils.finite_graded_set import InfiniteGradedSet
from yacop.utils.bitstuff import N0, binom_modp
from yacop.modules.module_base import SteenrodModuleBase
from yacop.categories import YacopLeftModules, YacopGradedObjects, YacopGradedSets
from yacop.modules.xitauring import XiTauRing
from sage.misc.lazy_attribute import lazy_attribute
from sage.misc.cachefunc import cached_method


class DicksonBase(SteenrodAlgebraBase):
    """
    Base class for DicksonDualSteenrodAlgebra and DicksonAlgebra
    """

    class Degrees(object):
        def __init__(self, prime, generic, ispos, index=None):
            self._prime = prime
            self._generic = generic
            self._ispos = ispos
            self._index = index

        def __getitem__(self, idx):
            if idx >= 2 * self._index:
                raise StopIteration
            idx = idx ^ 1
            fac = 2 if self._generic else 1
            if idx & 1:
                # tau_(idx-1)/2
                return (-(2 * self._prime ** ((idx - 1) >> 1) - 1), -1, 0)
            else:
                if self._ispos:
                    ind = idx >> 1
                    fac = -fac * self._prime ** (self._index - ind - 1)
                # xi_(idx/2+1)
                return (-fac * (self._prime ** (1 + (idx >> 1)) - 1), 0, 0)

    def __init__(
        self,
        prime,
        index,
        ispos=False,
        generic="auto",
        category=None,
        names=("zeta", "tau"),
        latexnames=("\\zeta", "\\tau"),
    ):
        if generic == "auto":
            generic = False if prime == 2 else True
        self._generic = generic
        degs = DicksonBase.Degrees(prime, generic, ispos=ispos, index=index)
        self._prime = prime
        self._index = index
        self._ispos = ispos
        A = (
            SteenrodAlgebra(prime)
            if prime > 2
            else SteenrodAlgebra(prime, generic=generic)
        )
        SteenrodAlgebraBase.__init__(
            self,
            XiTauRing(
                prime,
                numxi=index,
                numtau=index,
                degrees=degs,
                names=names,
                latexnames=latexnames,
            ),
            degs,
            None,
            A,
            left_action=True,
            right_action=False,
            category=category,
        )
        self._genpower = lambda g, e: self._R._genpower(g, e)

    def octants(self):
        return [(-1, -1, 0)] if not self._ispos else [(1, -1, 0)]

    def _is_sorted_by_t_degrees(self):
        return False if self._ispos else True

    def _max_exponents(self):
        if not self._generic:
            maxodd = 0
        else:
            maxodd = 1
        while True:
            yield maxodd
            yield Infinity

    def _monomial_gen_key(self, idx, expo=1):
        """
        TESTS::

           sage: from yacop.modules.dickson import *
           sage: D=DicksonDualSteenrodAlgebra(5,6)
           sage: for u in range(0,4):
           ....:     print(u,D._monomial_gen(u))
           0 1
           1 tau[0]
           2 zeta[1]
           3 tau[1]
           sage: D._tau(0)
           tau[0]
           sage: D._zetapower(3,5)
           zeta[3]**5
           sage: D._zetapower(0,2)
           1
        """
        return tuple([0 if x < idx else expo for x in range(1, idx + 1)])

    def _monomial_gen(self, idx, expo=1):
        return self._from_dict({self._monomial_gen_key(idx, expo): 1})

    def _toqp(self, elem):
        # hack: elem must be monomial with coefficient 1
        (elem,) = elem.monomial_coefficients()
        q = 0
        msk = 1
        for idx in elem[::2]:
            if idx:
                q = q | msk
            msk = msk << 1
        return q, elem[1::2]

    def gens(self):
        if self._generic:
            return [self._monomial_gen(i + 1) for (i, g) in enumerate(self._R.gens())]
        return [self._monomial_gen(i + 1) for (i, g) in enumerate(self._R.gens())][1::2]


class DicksonDualSteenrodAlgebra(DicksonBase):

    """
    TESTS::

        sage: from yacop.modules.dickson import *
        sage: from yacop import *
        sage: D=DicksonDualSteenrodAlgebra(5,3) ; D
        Dickson(3) dual Steenrod algebra at the prime 5
        sage: D is DicksonDualSteenrodAlgebra(5,3)
        True
        sage: D.inject_variables()
        Defining zeta, tau
        sage: zeta
        zeta-generator family of Dickson(3) dual Steenrod algebra at the prime 5
        sage: tau
        tau-generator family of Dickson(3) dual Steenrod algebra at the prime 5
        sage: zeta[2], tau[0]
        (zeta[2], tau[0])
        sage: zeta[1].parent() is D
        True
        sage: list(zeta)
        [1, zeta[1], zeta[2], zeta[3]]
        sage: list(tau)
        [tau[0], tau[1], tau[2]]
        sage: zeta[:2]
        [1, zeta[1]]
        sage: tau[:2]
        [tau[0], tau[1]]
        sage: zeta[1:7]
        [zeta[1], zeta[2], zeta[3]]
        sage: tau[0]*tau[2], tau[2]*tau[1], tau[1]*tau[1]
        (tau[0]*tau[2], 4*tau[1]*tau[2], 0)
        sage: tau[1:]
        [tau[1], tau[2]]
        sage: for u in zeta:
        ....:    print(u, u.t,u.e,u.s)
        1 0 0 0
        zeta[1] -8 0 0
        zeta[2] -48 0 0
        zeta[3] -248 0 0
        sage: for u in tau:
        ....:    print(u, u.t,u.e,u.s)
        tau[0] -1 -1 0
        tau[1] -9 -1 0
        tau[2] -49 -1 0
        sage: D.an_element()
        2 + 3*tau[0]
        sage: D.category()
        Category of yacop left module algebras over mod 5 Steenrod algebra, milnor basis
        sage: TestSuite(D).run()
        sage: D.bbox()
        region(-3 <= e <= 0, s = 0, -Infinity < t <= 0)
        sage: sorted(D.graded_basis(region(tmin=-30,tmax=-20)))
        [tau[1]*zeta[1]**2, zeta[1]**3, tau[0]*tau[1]*zeta[1]**2, tau[0]*zeta[1]**3]

        sage: D=DicksonDualSteenrodAlgebra(2,4)
        sage: zeta, = D.gens()
        sage: list(zeta)
        [1, zeta[1], zeta[2], zeta[3], zeta[4]]
        sage: [(u,u.t,u.e,u.s) for u in zeta]
        [(1, 0, 0, 0),
        (zeta[1], -1, 0, 0),
        (zeta[2], -3, 0, 0),
        (zeta[3], -7, 0, 0),
        (zeta[4], -15, 0, 0)]
        sage: sorted(D.graded_basis(t=-7))
        [zeta[3], zeta[1]*zeta[2]**2, zeta[1]**4*zeta[2], zeta[1]**7]

    """

    x = """
       sage: A = SteenrodAlgebra(5)
       sage: P,Q = A.P,A.Q_exp
       sage: [tau[1]*u for u in [Q(0,1),P(1),P(0)]]
       [1, tau[0], tau[1]]
       sage: [u*tau[1] for u in [Q(1),Q(0,1),P(0)]]
       [zeta[1], 1, tau[1]]
       sage: tensor((zeta[1],tau[1]))*P(1) == tensor((D.one(),tau[1])) + tensor((zeta[1],tau[0]))
       True
       sage: Q(1)*tensor((tau[2],tau[1])) == tensor((zeta[2],tau[1])) - tensor((tau[2],zeta[1]))
       True
       sage: TestSuite(D.category()).run()

       sage: E = DicksonDualSteenrodAlgebra(2) ; E
       dual Steenrod algebra at the prime 2
       sage: TestSuite(E).run()
       sage: E.inject_variables()
       Defining xi
       sage: xi
       xi-generator family of dual Steenrod algebra at the prime 2
       sage: for u in zeta[:4]:
       ....:    print(u, u.t,u.e,u.s)
       1 0 0 0
       zeta[1] -1 0 0
       zeta[2] -3 0 0
       zeta[3] -7 0 0
       sage: E.an_element()
       zeta[1] + zeta[1]**2
       sage: E.bbox()
       region(e = 0, s = 0, -Infinity < t <= 0)
       sage: sorted(E.graded_basis(region(t=-7)))
       [zeta[3], zeta[1]*zeta[2]**2, zeta[1]**4*zeta[2], zeta[1]**7]
       sage: TestSuite(E.category()).run()

       sage: F=DicksonDualSteenrodAlgebra(2,generic=True) ; F
       generic dual Steenrod algebra at the prime 2
       sage: sorted(F.graded_basis(t=-5))
       [tau[1]*zeta[1], tau[0]*zeta[1]**2]
       sage: TestSuite(F).run()

       sage: # regression test: make sure submodules are suspendable
       sage: E = DicksonDualSteenrodAlgebra(2) ; E.inject_variables()
       Defining xi
       sage: from yacop.modules.morph_module import SubModule
       sage: X = SubModule(E,(zeta[2],)) ; X
       submodule of dual Steenrod algebra at the prime 2 generated by (zeta[2],)
       sage: suspension(X,t=3) # (not) random, but it prints differently
       suspension (3,0,0) of submodule of dual Steenrod algebra at the prime 2 generated by (zeta[2],)
       sage: sorted(X.graded_basis())
       [zeta[2], zeta[1]**2, 1]

    """

    def __init__(self, prime, index, generic="auto", category=None):
        DicksonBase.__init__(
            self,
            prime,
            index,
            ispos=False,
            generic=generic,
            category=category,
            names=("zeta[{idx}]", "tau[{idx}]"),
            latexnames=("\\zeta_{{{idx}}}", "\\tau_{{{idx}}}"),
        )

    @lazy_attribute
    def _dicksonalgebra(self):
        """
        TESTS::

            sage: from yacop.modules.dickson import DicksonDualSteenrodAlgebra
            sage: D=DicksonDualSteenrodAlgebra(5,3)
            sage: D._dicksonalgebra
            Dickson-Mui algebra D(3) for prime 5

        """
        from yacop.modules.dickson import DicksonAlgebra

        return DicksonAlgebra(self._prime, self._index, generic=self._generic)

    def _repr_(self):
        # TODO support having numtau == 0
        gen = "generic " if self._prime == 2 and self._generic else ""
        return "%sDickson(%d) dual Steenrod algebra at the prime %d" % (
            gen,
            self._index,
            self._prime,
        )

    def _bbox(self):
        return region(tmax=0, emax=0, s=0, tmin=-Infinity, emin=-self._R.numtau)

    def variable_names(self):
        if not self._generic:
            return [
                "zeta",
            ]
        else:
            return ["zeta", "tau"]

    class GenFactory(SageObject):
        """
        TESTS::

            sage: from yacop.modules.dickson import DicksonDualSteenrodAlgebra
            sage: D=DicksonDualSteenrodAlgebra(5,3)
            sage: D.inject_variables()
            Defining zeta, tau
            sage: zeta[3]
            zeta[3]
            sage: zeta[4]
            Traceback (most recent call last):
            ...
            ValueError: no such generator
            sage: zeta[2:]
            [zeta[2], zeta[3]]
            sage: zeta[0:]
            [1, zeta[1], zeta[2], zeta[3]]
            sage: zeta[0:7]
            [1, zeta[1], zeta[2], zeta[3]]
            sage: zeta[1:7]
            [zeta[1], zeta[2], zeta[3]]
            sage: zeta[-1]
            Traceback (most recent call last):
            ...
            ValueError: no such generator


        """

        def __init__(self, par, even):
            self.par = par
            self.even = even

        def _repr_(self):
            v = "zeta" if self.even else "tau"
            return "%s-generator family of %s" % (v, self.par)

        def __getitem__(self, val):
            max = self.par._index
            numtau = self.par._R.numtau
            if self.even:
                max += 1
            if isinstance(val, slice):
                start = 0 if val.start is None else val.start
                stop = max if val.stop is None else val.stop
                step = 1 if val.step is None else val.step
                if start < 0:
                    raise ValueError("no such generator")
                if stop > max:
                    stop = max
                return [self[u] for u in range(start, stop, step)]
            idx = val << 1
            if not self.even:
                idx = idx + 1
            else:
                if idx == 0:
                    return self.par.one()
                elif idx < 0:
                    raise ValueError("no such generator")
                idx = idx - 2
            idx = idx ^ 1
            if idx >= 2 * self.par._index:
                raise ValueError("no such generator")
            if 0 == numtau:
                idx = idx >> 1
                return self.par._monomial_gen(idx + 1)
            return self.par._monomial_gen(idx + 1)

        def __iter__(self):
            return self[0:].__iter__()

    def _zetapower(self, idx, pow=1):
        return self._monomial_gen(idx << 1, pow)

    def _tau(self, idx):
        return self._monomial_gen((idx << 1) + 1)

    def zeta(self, idx):
        """
        TESTS::

            sage: from yacop.modules.dickson import DicksonDualSteenrodAlgebra
            sage: D=DicksonDualSteenrodAlgebra(3,5)
            sage: D.zeta(3)
            zeta[3]
            sage: D.zeta(0)
            1
        """
        if idx < 0:
            raise ValueError("negative index not allowed")
        if idx > self._index:
            raise ValueError("monomial not in Dickson algebra")
        return self._zetapower(idx)

    def tau(self, idx):
        """
        TESTS::

           sage: from yacop.modules.dickson import DicksonDualSteenrodAlgebra
           sage: D=DicksonDualSteenrodAlgebra(11,4)
           sage: D.tau(3)
           tau[3]
           sage: D.tau(-1)
           1
        """
        if not self._generic:
            raise ValueError("tau generator not defined in %s" % self)
        if idx < -1:
            raise ValueError("index < -1 not allowed")
        if idx > self._index:
            raise ValueError("monomial not in Dickson algebra")
        return self._tau(idx)

    def gens(self):
        ans = [
            DicksonDualSteenrodAlgebra.GenFactory(self, 1),
        ]
        if self._generic:
            ans.append(DicksonDualSteenrodAlgebra.GenFactory(self, 0))
        return ans

    def _coproduct_gen(self, idx):
        """
        TESTS::

           sage: from yacop.modules.dickson import *
           sage: D=DicksonDualSteenrodAlgebra(5,6)
           sage: for u in (0,..,6):
           ....:    print("%-6s"%D._monomial_gen(u+1), "->", list(D._coproduct_gen(u)))
           tau[0] -> [(tau[0], 1), (1, tau[0])]
           zeta[1]  -> [(zeta[1], 1), (1, zeta[1])]
           tau[1] -> [(tau[1], 1), (zeta[1], tau[0]), (1, tau[1])]
           zeta[2]  -> [(zeta[2], 1), (zeta[1]**5, zeta[1]), (1, zeta[2])]
           tau[2] -> [(tau[2], 1), (zeta[2], tau[0]), (zeta[1]**5, tau[1]), (1, tau[2])]
           zeta[3]  -> [(zeta[3], 1), (zeta[2]**5, zeta[1]), (zeta[1]**25, zeta[2]), (1, zeta[3])]
           tau[3] -> [(tau[3], 1), (zeta[3], tau[0]), (zeta[2]**5, tau[1]), (zeta[1]**25, tau[2]), (1, tau[3])]
        """
        if idx & 1:
            n = (idx + 1) >> 1
            # Delta(xi_n)  = sum xi_{n-i}^{p^i}*xi_i
            ppow = 1
            for i in range(0, n + 1):
                yield self._zetapower(n - i, ppow), self._zetapower(i)
                ppow = ppow * self._prime
        else:
            n = idx >> 1
            # Delta(tau_n) = sum xi_{n-i}^{p^i}*tau_i + tau_n*1
            ppow = 1
            yield self._tau(n), self._zetapower(0)
            for i in range(0, n + 1):
                yield self._zetapower(n - i, ppow), self._tau(i)
                ppow = ppow * self._prime

    def _left_steenrod_coaction_milnor_gen(self, idx, maxQ, maxP):
        for (ff, sf) in self._coproduct_gen(idx):
            q, p = self._toqp(sf)
            yield self._coaction_tensor(ff, q, p)

    def _right_steenrod_coaction_milnor_gen(self, idx, maxQ, maxP):
        for (ff, sf) in self._coproduct_gen(idx):
            q, p = self._toqp(ff)
            yield self._coaction_tensor(sf, q, p)


class DicksonAlgebra(DicksonBase):
    def __init__(self, prime, index, generic="auto", category=None):
        """
        TESTS::

            sage: from yacop.modules.dickson import DicksonAlgebra
            sage: D = DicksonAlgebra(2,4) ; D
            Dickson algebra D(4) for prime 2
            sage: D.bbox()
            region(e = 0, s = 0, 0 <= t < +Infinity)
            sage: D.inject_variables()
            Defining d8, d12, d14, d15
            sage: d12.parent() is D
            True
            sage: list(D.graded_basis(t=30))
            [d15**2, d8**2*d14]
            sage: TestSuite(D).run()

            sage: E = DicksonAlgebra(3,3) ; E
            Dickson-Mui algebra D(3) for prime 3
            sage: E.inject_variables()
            Defining tau0, d36, tau1, d48, tau2, d52
            sage: for u in E.gens():
            ....:     print ("%-5s %s"%(u,(u.t,u.e,u.s)))
                tau0  (-1, -1, 0)
                d36   (36, 0, 0)
                tau1  (-5, -1, 0)
                d48   (48, 0, 0)
                tau2  (-17, -1, 0)
                d52   (52, 0, 0)
            sage: E.bbox()
            region(-3 <= e <= 0, s = 0, -23 <= t < +Infinity)
            sage: for deg in [-5,-23,30,52,47,123]:
            ....:     print("%-5d %s" % (deg, list(E.graded_basis(t=deg))))
            -5    [tau1]
            -23   [tau0*tau1*tau2]
            30    [tau0*tau1*d36, tau0*tau2*d48, tau1*tau2*d52]
            52    [d52]
            47    [tau1*d52, tau0*d48]
            123   [tau0*d36**2*d52, tau2*d36*d52**2]
            sage: TestSuite(E).run()

            sage: # the following failes once
            sage: A=SteenrodAlgebra(3)
            sage: A.P(1)*(A.Q(0)*(tau0*tau1))
            2*tau0*d52
            sage: (A.P(1)*A.Q(0))*(tau0*tau1)
            2*tau0*d52

            sage: F=DicksonAlgebra(5,2,generic=False); F
            Dickson algebra D(2) for prime 5
            sage: F.inject_variables()
            Defining d20, d24
            sage: F.bbox()
            region(e = 0, s = 0, 0 <= t < +Infinity)
            sage: sorted(F.graded_basis(tmax=44))
            [1, d24, d20, d20*d24, d20**2]
            sage: TestSuite(F).run()

            sage: G=DicksonAlgebra(2,2,generic=True); G
            Dickson-Mui algebra D(2) for prime 2
            sage: G.inject_variables()
            Defining tau0, d4, tau1, d6
            sage: G.bbox()
            region(-2 <= e <= 0, s = 0, -4 <= t < +Infinity)
            sage: sorted(G.graded_basis(tmax=2))
            [1, tau1, tau1*d4, tau0, tau0*tau1, tau0*tau1*d6, tau0*tau1*d4]
            sage: TestSuite(G).run()

        """
        DicksonBase.__init__(
            self,
            prime,
            index,
            ispos=True,
            generic=generic,
            category=category,
            names=("d{deg}", "tau{idx}"),
            latexnames=("d_{{{deg}}}", "\\tau_{{{idx}}}"),
        )

    def variable_names(self):
        return [str(u) for u in self.gens()]

    def _repr_(self):
        gen = "-Mui" if self._generic else ""
        return "Dickson%s algebra D(%d) for prime %d" % (gen, self._index, self._prime)

    @cached_method
    def _bbox(self):
        emin = 0 if not self._generic else -self._R.numtau
        tmin = sum(u.t for u in self.gens() if u.t < 0)
        return region(tmin=tmin, emax=0, s=0, tmax=Infinity, emin=emin)

    @lazy_attribute
    def _peterson_factory(self):
        from yacop.modules.dickson import PetersonPolynomials

        return PetersonPolynomials(self._prime, self._index)

    def peterson(self, idx, coeff=1):
        """
        Peterson element omega_idx

        TESTS::

            sage: from yacop.modules.dickson import DicksonAlgebra
            sage: D = DicksonAlgebra(3,3)
            sage: [D.peterson(i) for i in (9,12,13)]
            [d36, d48, d52]
            sage: D = DicksonAlgebra(2,3)
            sage: for i in range(4,30):
            ....:     if i in [5,9,17,]: continue
            ....:     print( "%-3d %s" % (i,D.peterson(i)))
            4   d4
            6   d6
            7   d7
            8   d4**2
            10  d4*d6
            11  d4*d7
            12  d6**2
            13  d6*d7
            14  d7**2
            15  0
            16  d4**4
            18  d6**3 + d4*d7**2 + d4**3*d6
            19  d6**2*d7 + d4**3*d7
            20  d4**2*d6**2
            21  d7**3 + d4**2*d6*d7
            22  d4**2*d7**2
            23  0
            24  d6**4
            25  d6**3*d7 + d4*d7**3
            26  d6**2*d7**2
            27  0
            28  d7**4
            29  0
            sage: D.peterson(17)
            Traceback (most recent call last):
            ...
            ValueError: Peterson element 17 not in Dickson algebra D(3) for prime 2

        """
        GF = self.base_ring()
        dec = PetersonPolynomials.decompose(self._prime, idx)
        comp = []
        startpow = self._prime ** (self._index - 1)
        for (cf, expos) in dec:
            if len(expos) > self._index:
                continue
            pow = startpow
            key = []
            for e in expos:
                if e % pow != 0:
                    raise ValueError("Peterson element %d not in %s" % (idx, self))
                key.append(0)
                key.append(e // pow)
                pow //= self._prime
            comp.append((tuple(key), GF(coeff * cf)))
        return self._from_dict(dict(comp))

    def _zetapower(self, idx, pow=1):
        """
        TESTS::

            sage: from yacop.modules.dickson import DicksonAlgebra
            sage: D = DicksonAlgebra(2,4)
            sage: [D._zetapower(i) for i in range(5)]
            [1, d14*d15**(-1), d12*d15**(-1), d8*d15**(-1), d15**(-1)]

        """
        if idx == 0:
            return self.one()
        x = self._monomial_gen_key(2 * self._index, -pow)
        if idx < self._index:
            y = list(x)
            y[2 * (self._index - idx) - 1] += pow
            x = tuple(y)
        elif idx > self._index:
            raise ValueError("zeta%d not in %s" % (idx, self))
        return self._from_dict({x: 1})

    def _xipower(self, idx, pow=1):
        """
        TESTS::

            sage: from yacop.modules.dickson import DicksonAlgebra
            sage: D = DicksonAlgebra(2,3)
            sage: [D._xipower(i) for i in (0,1,2,3)]
            [1,
            d6*d7**(-1),
            d6**3*d7**(-3) + d4*d7**(-1),
            d7**(-1) + d6**7*d7**(-7) + d4*d6**4*d7**(-5) + d4**2*d6*d7**(-3)]
            sage: D = DicksonAlgebra(3,2)
            sage: [D._xipower(i) for i in (0,1,2)]
            [1, 2*d12*d16**(-1), 2*d16**(-1) + d12**4*d16**(-4)]

        """
        # FIXME: compute this more intelligently, e.g. just cache xi^k with k<p
        return self.__xi(idx, pow)

    @cached_method
    def __xi(self, idx, pow):
        if idx == 0:
            return self.one()
        elif idx > self._index:
            raise ValueError("xi%d not in %s" % (idx, self))
        if pow > 1:
            return self.product(self.__xi(idx, pow - 1), self.__xi(idx, 1))
        p = self._prime
        return -self.sum(
            self.product(self.__xi(j, 1), self._zetapower(idx - j, p ** j))
            for j in range(idx)
        )

    def admissible_action(self, redpow, elem, debug=False):
        """
        Compute redpow * elem using admissible matrices
        """
        from yacop.utils.admissible_matrices import AdmissibleMatrices

        isgen = redpow.parent().is_generic()
        zpad = [
            0,
        ] * self._index
        ans = []
        for (key, cf) in redpow:
            if isgen:
                (epart, expos) = key
                if len(epart) > 0:
                    raise ValueError("exterior multiplications not implemented yet")
            else:
                expos = key
            # print "redpow contains", (key,cf), "expos=",expos
            for (c, a, cols, diag) in AdmissibleMatrices(
                self._prime, expos, maxn=self._index
            ).enumerate():
                if debug:
                    print("admissible matrix, coeff=%d\n%s" % (c, a))
                for (dkey, dcf) in elem:
                    ncf = c * dcf * cf
                    for _ in [
                        0,
                    ]:
                        dkey = list(dkey) + zpad + zpad
                        if max(dkey[0::2]) != 0:
                            raise ValueError("exterior part not implemented yet")
                        rexpos = dkey[1::2]
                        zexpos = list(reversed(rexpos[0 : self._index - 1]))
                        zexpos = [-1 - _ for _ in zexpos] + [
                            -1 + sum(zexpos) + rexpos[self._index - 1]
                        ]
                        if debug:
                            print(
                                "%s = zeta(%s)"
                                % (self._from_dict({tuple(dkey): dcf}), zexpos)
                            )
                        zrems = [a - b for (a, b) in zip(zexpos, cols[1:] + zpad)]
                        if debug:
                            print("zeta-remainder = ", zrems)
                        for (dterm, zterm) in zip(diag, zrems):
                            ncf *= binom_modp(self._prime, dterm + zterm, dterm)
                            if ncf.is_zero():
                                break
                        if debug:
                            print("coefficient=", ncf)
                        if ncf.is_zero():
                            continue
                        newzeta = [a + b for (a, b) in zip(diag + zpad, zrems)]
                        newexpo = list(
                            reversed([-1 - a for a in newzeta[0 : self._index - 1]])
                        )
                        newexpo.append(1 + newzeta[self._index - 1] - sum(newexpo))
                        newkey = [(0, _) for _ in newexpo]
                        newkey = [_ for j in newkey for _ in j]
                        while newkey[-1] == 0:
                            newkey.pop()
                        ans.append(self._from_dict({tuple(newkey): ncf}))
        return self.sum(ans)

    def __action_exponents(self, p, n, maxP, isconjugate=False):
        """
        generator for exponent sequences R such that the multinomial coefficient

           (p r1 | p^2 r2 | p^3 r3 | ... | (p-1)n - sum rk)

        is not zero and R is dominated by maxP
        """
        # Question: can we enforce sum rk <= (p-1)n?
        for (cf, exp, dg, psum, esum) in self.__action_exponents2(p, maxP, 0, 0):
            # the flag isconjugate switches between ordinary and conjugate action
            if isconjugate:
                c2 = binom_modp(p, -n * (p - 1), psum)
            else:
                c2 = binom_modp(p, psum + n * (p - 1) - esum, psum)
            if c2 != 0:
                yield (c2 * cf, exp, dg)

    def __action_exponents2(self, p, maxP, partialsum, expsum):
        idx = len(maxP)
        if idx > 0:
            ppow = p ** idx
            opdeg = (ppow - 1) // (p - 1)
            idx = idx - 1
            for e in range(maxP[idx] + 1):
                epow = e * ppow
                ps2 = partialsum + epow
                cf = binom_modp(p, ps2, epow)
                if cf != 0:
                    for (c, exp, dg, ps, es) in self.__action_exponents2(
                        p, maxP[0:idx], ps2, expsum + e
                    ):
                        yield (
                            c * cf,
                            exp
                            + [
                                e,
                            ],
                            dg + e * opdeg,
                            ps,
                            es,
                        )
        else:
            yield (1, [], 0, partialsum, expsum)

    def _left_steenrod_coaction_milnor_gen(self, idx, maxQ, maxP):
        """
        implementation of the Steenrod algebra action

        TESTS::

            sage: from yacop.modules.dickson import DicksonAlgebra
            sage: from yacop.utils.region import region
            sage: D=DicksonAlgebra(2,3)
            sage: D._manual_test_left_action(region(tmax=20,tmin=15),opdeg=5) # long time
            126 non-zero multiplications checked
            sage: for g in D.gens():
            ....:    for n in range(50):
            ....:        x = Sq(n)*g
            ....:        if x != 0:
            ....:             print("|%7s*%-2s = %s" % (Sq(n),g,x))
            |      1*d4 = d4
            |  Sq(2)*d4 = d6
            |  Sq(3)*d4 = d7
            |  Sq(4)*d4 = d4**2
            |      1*d6 = d6
            |  Sq(1)*d6 = d7
            |  Sq(4)*d6 = d4*d6
            |  Sq(5)*d6 = d4*d7
            |  Sq(6)*d6 = d6**2
            |      1*d7 = d7
            |  Sq(4)*d7 = d4*d7
            |  Sq(6)*d7 = d6*d7
            |  Sq(7)*d7 = d7**2

            sage: E=DicksonAlgebra(2,4,generic=True) ; E.inject_variables()
            Defining tau0, d16, tau1, d24, tau2, d28, tau3, d30
            sage: E._manual_test_left_action(region(tmax=12,tmin=10),opdeg=15) # long time
            384 non-zero multiplications checked
            sage: A=SteenrodAlgebra(2,generic=True)
            sage: [(i,A.P(i)*d30) for i in range(60) if A.P(i)*d30 != 0]
            [(0, d30), (8, d16*d30), (12, d24*d30), (14, d28*d30), (15, d30**2)]
            sage: [(i,A.P(i)*d16) for i in range(60) if A.P(i)*d16 != 0]
            [(0, d16), (4, d24), (6, d28), (7, d30), (8, d16**2)]
            sage: [(g,A.Q(0)*g) for g in E.gens()]
            [(tau0, 1),
             (d16, 0),
             (tau1, d28*d30**(-1)),
             (d24, 0),
             (tau2, d28**3*d30**(-3) + d24*d30**(-1)),
             (d28, 0),
             (tau3,
             d28**7*d30**(-7) + d24*d28**4*d30**(-5) + d24**2*d28*d30**(-3) + d16*d30**(-1)),
             (d30, 0)]
            sage: [(g,A.Q(1)*g) for g in E.gens()[::2]]
            [(tau0, 0),
             (tau1, 1),
             (tau2, d28**2*d30**(-2)),
             (tau3, d28**6*d30**(-6) + d24**2*d30**(-2))]
            sage: [(g,A.Q(2)*g) for g in E.gens()[::2]]
            [(tau0, 0), (tau1, 0), (tau2, 1), (tau3, d28**4*d30**(-4))]
            sage: E._manual_test_left_action(region(tmax=10,tmin=-10)) #long time
            2044 non-zero multiplications checked

            sage: F = DicksonAlgebra(3, 2)
            sage: F._manual_test_left_action(region(tmax=20),opdeg=20)
            479 non-zero multiplications checked
            sage: A = SteenrodAlgebra(3)
            sage: for g in F.gens()[1::2]:
            ....:    for n in range(50):
            ....:        op = A.P(n)
            ....:        x = op*g
            ....:        if x != 0:
            ....:             print("|%7s*%-3s = %s" % (op,g,x))
            |      1*d12 = d12
            |   P(1)*d12 = 2*d16
            |   P(3)*d12 = d12**2
            |   P(4)*d12 = d12*d16
            |   P(5)*d12 = d16**2
            |   P(6)*d12 = d12**3
            |      1*d16 = d16
            |   P(3)*d16 = d12*d16
            |   P(4)*d16 = 2*d16**2
            |   P(6)*d16 = d12**2*d16
            |   P(7)*d16 = d12*d16**2
            |   P(8)*d16 = d16**3


        """
        if idx & 1:
            num = (idx + 1) >> 1
            expo = self._prime ** (self._index - num)
            n = 0
            while num:
                num = num - 1
                n += self._prime ** num * expo
            # now idx = self.peterson(n)
            # print "exponents(n=%d,maxP=%s)=%s" % (n,maxP,list(self.__action_exponents(self._prime, n, maxP)))
            for (cf, expos, deg) in self.__action_exponents(self._prime, n, maxP):
                if cf:
                    yield self._coaction_tensor(
                        self.peterson(n + deg, coeff=cf), 0, expos
                    )
        else:
            n = idx >> 1
            # Delta(tau_n) = sum zeta_{n-i}^{p^i}*tau_i + tau_n*1
            ppow = 1
            yield self._coaction_tensor(self._monomial_gen(idx + 1), 0, ())
            # print "Delta(tau%d)" % n
            # print self._coaction_tensor(self._monomial_gen(idx+1), 0, ())
            for i in range(0, n + 1):
                # print self._coaction_tensor(self._zetapower(n - i, ppow), 1<<i, ())
                yield self._coaction_tensor(self._xipower(n - i, ppow), 1 << i, ())
                ppow = ppow * self._prime

    def _left_conjugate_steenrod_coaction_milnor_gen(self, idx, maxQ, maxP):
        """
        implementation of the Steenrod algebra action via conjugates

        TESTS::

            sage: from yacop.modules.dickson import DicksonAlgebra
            sage: from yacop.utils.region import region
            sage: E=DicksonAlgebra(3,2)
            sage: E._manual_test_left_conj_action(region(tmax=30,emax=30))
        """
        if idx & 1:
            num = (idx + 1) >> 1
            expo = self._prime ** (self._index - num)
            n = 0
            while num:
                num = num - 1
                n += self._prime ** num * expo
            # now idx = self.peterson(n)
            # print "exponents(n=%d,maxP=%s)=%s" % (n,maxP,list(self.__action_exponents(self._prime, n, maxP)))
            for (cf, expos, deg) in self.__action_exponents(
                self._prime, n, maxP, isconjugate=True
            ):
                if cf:
                    yield self._coaction_tensor(
                        self.peterson(n + deg, coeff=cf), 0, expos
                    )
        else:
            # FIXME: the exterior part is wrong
            n = idx >> 1
            # Delta(tau_n) = sum zeta_{n-i}^{p^i}*tau_i + tau_n*1
            ppow = 1
            yield self._coaction_tensor(self._monomial_gen(idx + 1), 0, ())
            for i in range(0, n + 1):
                yield self._coaction_tensor(self._zetapower(n - i, ppow), 1 << i, ())
                ppow = ppow * self._prime

    def _left_conjugate_coaction_on_basis(self, a, maxq, maxp):
        return self._coaction_helper(
            self._left_conjugate_steenrod_coaction_milnor_gen,
            self._factor_key(a, 0 if len(maxp) == 0 else max(maxp)),
            maxq,
            maxp,
        )

    def left_steenrod_action_milnor_conj(self, a, m):
        """
        TESTS::

            sage: from yacop.modules.dickson import DicksonAlgebra
            sage: from yacop.utils.region import region
            sage: D=DicksonAlgebra(2,3) ; D.inject_variables()
            Defining d4, d6, d7
            sage: Sq(18,6) % d4**5
            d7**8 + d4**4*d6**2*d7**4

        """
        return self._act_from_coact(self._left_conjugate_coaction_on_basis, a, m)

    def _restriction_basis(self, dest, key):
        #print("_restriction_basis",dest,key)
        idx = dest._index
        if len(key) > 2 * idx:
            return dest.zero()
        ans = []
        for (i, x) in enumerate(key):
            ans.append(x if 0 == i & 1 else self._prime * x)
        while len(ans) and 0 == ans[-1]:
            ans.pop()
        return dest._from_dict({tuple(ans): self.base_ring().one()})

    @cached_method
    def restriction(self, other):
        """
        TESTS::

            sage: from yacop.modules.dickson import DicksonAlgebra
            sage: D=DicksonAlgebra(3,3)
            sage: r = D.restriction(DicksonAlgebra(3,2)) ; r
            restriction from Dickson-Mui algebra D(3) for prime 3 to Dickson-Mui algebra D(2) for prime 3
            sage: D.inject_variables()
            Defining tau0, d36, tau1, d48, tau2, d52
            sage: r(tau0*tau1)
            tau0*tau1
            sage: r(tau0*tau1*tau2)
            0
            sage: r(tau0*tau1*d48)
            tau0*tau1*d16**3

            sage: D=DicksonAlgebra(2,3) ; D.inject_variables()
            Defining d4, d6, d7
            sage: r = D.restriction(DicksonAlgebra(2,2))
            sage: r(d4), r(d6), r(d7)
            (d2**2, d3**2, 0)

            sage: D=DicksonAlgebra(3,3) ; D
            Dickson-Mui algebra D(3) for prime 3
            sage: E=DicksonAlgebra(3,2) ; E
            Dickson-Mui algebra D(2) for prime 3
            sage: f=D.restriction(E) ; f
            restriction from Dickson-Mui algebra D(3) for prime 3 to Dickson-Mui algebra D(2) for prime 3
            sage: for x in list(D.graded_basis(tmax=20)):
            ....:     y = f(x) # check this does not raise an exception

        """
        if not isinstance(other, DicksonAlgebra):
            raise ValueError("Dickson algebra instance expected")
        if not other._prime == self._prime:
            raise ValueError("prime mismatch")
        if other._index > self._index:
            raise ValueError("restriction from %s to %s not defined" % (self, other))
        ans = self.module_morphism(
            codomain=other, on_basis=lambda x: self._restriction_basis(other, x)
        )
        ans.rename("restriction from %s to %s" % (self, other))
        return ans

    def _transfer_basis(self, dest, key):
        raise NotImplementedError("not implemented")

    @cached_method
    def transfer(self, other):
        """
        TESTS::

            sage: from yacop.modules.dickson import DicksonAlgebra
            sage: D=DicksonAlgebra(3,1)
            sage: t = D.transfer(DicksonAlgebra(3,5)) ; t
            transfer from Dickson-Mui algebra D(1) for prime 3 to Dickson-Mui algebra D(5) for prime 3

        """
        if not isinstance(other, DicksonAlgebra):
            raise ValueError("Dickson algebra instance expected")
        if not other._prime == self._prime:
            raise ValueError("prime mismatch")
        if other._index < self._index:
            raise ValueError("transfer from %s to %s not defined" % (self, other))
        ans = self.module_morphism(
            codomain=other, on_basis=lambda x: self._transfer_basis(other, x)
        )
        ans.rename("transfer from %s to %s" % (self, other))
        return ans


class PetersonPolynomials(SageObject):
    """
    A class that computes the Peterson polynomials and their expression as
    Dickson polynomials.
    """

    def __init__(self, p, n):
        """
        TESTS::

            sage: from yacop.modules.dickson import PetersonPolynomials
            sage: P=PetersonPolynomials(3,2) ; P
            Peterson element factory for prime 3, index 2
            sage: for idx in range(20):
            ....:     print("%-3d : %s" % (idx,P.omega(idx)))
            0   : 1
            1   : x1^2 + x2^2
            2   : x1^4 + x1^2*x2^2 + x2^4
            3   : x1^6 + x1^4*x2^2 + x1^2*x2^4 + x2^6
            4   : x1^6*x2^2 + x1^4*x2^4 + x1^2*x2^6
            5   : -x1^10 + x1^6*x2^4 + x1^4*x2^6 - x2^10
            6   : x1^12 - x1^10*x2^2 + x1^6*x2^6 - x1^2*x2^10 + x2^12
            7   : x1^12*x2^2 - x1^10*x2^4 - x1^4*x2^10 + x1^2*x2^12
            8   : x1^12*x2^4 - x1^10*x2^6 - x1^6*x2^10 + x1^4*x2^12
            9   : x1^18 + x1^12*x2^6 + x1^6*x2^12 + x2^18
            10  : x1^18*x2^2 + x1^10*x2^10 + x1^2*x2^18
            11  : x1^18*x2^4 - x1^12*x2^10 - x1^10*x2^12 + x1^4*x2^18
            12  : x1^18*x2^6 + x1^12*x2^12 + x1^6*x2^18
            13  : 0
            14  : x1^28 - x1^18*x2^10 - x1^10*x2^18 + x2^28
            15  : -x1^30 + x1^28*x2^2 + x1^18*x2^12 + x1^12*x2^18 + x1^2*x2^28 - x2^30
            16  : -x1^30*x2^2 + x1^28*x2^4 + x1^4*x2^28 - x1^2*x2^30
            17  : -x1^30*x2^4 + x1^28*x2^6 + x1^6*x2^28 - x1^4*x2^30
            18  : x1^36 - x1^30*x2^6 + x1^18*x2^18 - x1^6*x2^30 + x2^36
            19  : x1^36*x2^2 - x1^28*x2^10 - x1^10*x2^28 + x1^2*x2^36

        """
        from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
        from yacop.modules.classifying_spaces import BZpGeneric
        from sage.categories.tensor import tensor

        self.p = p
        self.n = n
        self.B = BZpGeneric(p)
        factors = tuple(
            [
                self.B,
            ]
            * n
        )
        self.BT = tensor(factors)
        self.tc = self.BT.tensor_constructor(factors)
        deg = -1
        fac = 2  # if p>2 else 1
        self.b = self.B.monomial(fac * deg)
        self.binv = self.B.monomial(-fac * deg)
        self.bt = tensor(
            [
                self.b,
            ]
            * n
        )
        self.bti = tensor(
            [
                self.binv,
            ]
            * n
        )
        self.P = SteenrodAlgebra(p, generic=True).P
        self.Q = PolynomialRing(
            GF(p),
            ["x%d" % (i + 1) for i in range(n)]
            + [
                "t",
            ],
        )

    def _repr_(self):
        return "Peterson element factory for prime %d, index %d" % (self.p, self.n)

    @cached_method
    def dicksons(self):
        """
        TESTS::

            sage: from yacop.modules.dickson import PetersonPolynomials
            sage: P=PetersonPolynomials(2,3)
            sage: for p in P.dicksons():
            ....:     print(p)
            x1^4*x2^2*x3 + x1^2*x2^4*x3 + x1^4*x2*x3^2 + x1*x2^4*x3^2 + x1^2*x2*x3^4 + x1*x2^2*x3^4
            x1^4*x2^2 + x1^2*x2^4 + x1^4*x2*x3 + x1*x2^4*x3 + x1^4*x3^2 + x1^2*x2^2*x3^2 + x2^4*x3^2 + x1^2*x3^4 + x1*x2*x3^4 + x2^2*x3^4
            x1^4 + x1^2*x2^2 + x2^4 + x1^2*x2*x3 + x1*x2^2*x3 + x1^2*x3^2 + x1*x2*x3^2 + x2^2*x3^2 + x3^4
            sage: P=PetersonPolynomials(5,2)
            sage: for p in P.dicksons():
            ....:     print(p)
            x1^20*x2^4 + x1^16*x2^8 + x1^12*x2^12 + x1^8*x2^16 + x1^4*x2^20
            x1^20 + x1^16*x2^4 + x1^12*x2^8 + x1^8*x2^12 + x1^4*x2^16 + x2^20

        """
        xi = self.Q.gens()[:-1]
        t = self.Q.gens()[self.n]
        pol = self.Q.prod(
            t + self.Q.sum(a * x for (a, x) in zip(cf, xi))
            for cf in GF(self.p) ** self.n
        )
        return [
            pol.coefficient(t ** (self.p ** i)) * (-1) ** (self.n - i)
            for i in range(self.n)
        ]

    def is_invariant(self, qelem):
        """
        TESTS::

            sage: from yacop.modules.dickson import PetersonPolynomials
            sage: P=PetersonPolynomials(2,3)
            sage: [P.is_invariant(d) for d in P.dicksons()]
            [True, True, True]
            sage: [(n,P.is_invariant(P.omega(n))) for n in range(10)]
            [(0, True),
             (1, False),
             (2, False),
             (3, False),
             (4, True),
             (5, False),
             (6, True),
             (7, True),
             (8, True),
             (9, False)]

        """
        if self.n == 1:
            return True
        Q = self.Q
        x1, x2 = Q.gens()[0:2]
        # we already know the element is symmetric in the variables
        # so we only check invariance under x1 -> x1+x2
        return (qelem - qelem.subs({x1: x1 + x2})).is_zero()  #

    def toQ(self, x):
        return self.Q.sum(
            cf * self.Q.prod(a ** (e >> 1) for (a, e) in zip(self.Q.gens(), expo))
            for (expo, cf) in x
        )

    def opelem(self, op):
        return self.toQ((op * self.bt) * self.bti)

    def opconjelem(self, op):
        return self.toQ((op % self.bt) * self.bti)

    @cached_method
    def omega(self, n):
        return self._omega_fast(n)

    def _omega_safe(self, n):
        return self.opelem(self.P(n).antipode())

    def _omega_exponents(self, sum, len):
        if len == 1:
            cf = self.gamma(sum)
            if cf:
                yield (
                    cf,
                    [
                        sum,
                    ],
                )
            return
        if len > 1:
            for smd in range(sum + 1):
                cf = self.gamma(smd)
                if cf:
                    for (c, x) in self._omega_exponents(sum - smd, len - 1):
                        yield (
                            cf * c,
                            [
                                smd,
                            ]
                            + x,
                        )

    def _omega_fast(self, n):
        """
        TESTS::

            sage: from yacop.modules.dickson import PetersonPolynomials
            sage: P=PetersonPolynomials(5,3)
            sage: for n in range(25,31):
            ....:     assert P._omega_safe(n) == P._omega_fast(n)
            sage: P=PetersonPolynomials(2,4)
            sage: for n in range(10,13):
            ....:     assert P._omega_safe(n) == P._omega_fast(n)

        """
        from sage.combinat.integer_vector_weighted import WeightedIntegerVectors
        from sage.misc.misc_c import prod

        pmo = self.p - 1
        ans = []
        for (cf, expos) in self._omega_exponents(n, self.n):
            if 0 == cf % self.p:
                continue
            ans.append(
                cf * self.Q.prod(a ** (pmo * e) for (a, e) in zip(self.Q.gens(), expos))
            )
        return self.Q.sum(ans)

    @staticmethod
    def _milnor_basis(p, n):
        from sage.algebras.steenrod.steenrod_algebra_bases import milnor_basis

        if p == 2:
            for x in milnor_basis(n, 2):
                yield x
        else:
            for (x, y) in milnor_basis(n, p):
                if len(x) == 0:
                    yield y

    def gamma(self, n):
        """
        the gamma(n) in the definition of omega(n)
        """
        return binom_modp(self.p, -(self.p - 1) * n, n)

    @staticmethod
    def decompose(p, n):
        """
        Decompose a omega_n into a product of Dicksonians
        """

        inv = p ** (p - 2)
        tdeg = 2 * (p - 1) if p > 2 else 1
        pmo = p - 1
        # FIXME: why does this not depend on the generic/non-generic flag for p=2?
        for expos in PetersonPolynomials._milnor_basis(p, tdeg * n):
            sum = 0
            cf = 1
            for a in expos:
                sum += a
                cf *= binom_modp(p, sum, a)
                if 0 == cf:
                    break
            if 0 == cf:
                continue
            cf *= binom_modp(p, -n * pmo, sum)
            if 0 != cf:
                yield [cf, expos]

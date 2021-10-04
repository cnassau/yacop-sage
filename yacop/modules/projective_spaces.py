r"""
Cohomology of projective spaces

AUTHORS: - Christian Nassau (2011-05-13: version 1.0)

Here we implement projective spaces as modules over the 2-primary Steenrod algebra.

EXAMPLES AND TESTS:

The construction of these modules is straightforward::

    sage: from yacop.modules.projective_spaces import *
    sage: M=ComplexProjectiveSpace(12,prefix='w')
    sage: print(M)
    mod 2 cohomology of complex projective space P^{12}
    sage: M.an_element()
    w + w^3
    sage: N=RealProjectiveSpace(prefix='x')
    sage: N.inject_variables()
    Defining x
    sage: Sq(1)*x == x^2
    True
    sage: Sq(4)*Sq(2)*x^2 == x^8
    True
    sage: Sq(1,2) % x == x^8
    True
    sage: 5*x == x, 0*x
    (True, 0)
    sage: M.inject_variables()
    Defining w
    sage: Sq(4)*w^2
    w^4

The `t`-degree is the usual internal degree, whereas the Bockstein degree `e` and the
homological degree `s` are both always zero::

    sage: w.t,w.e,w.s
    (2, 0, 0)
    sage: (x^3).t
    3

Negative dimensional classes can also be constructed::

    sage: X=RealProjectiveSpace(botexp=-10,prefix='u')
    sage: X.inject_variables()
    Defining u
    sage: g=X.monomial(-10)
    sage: print(g)
    u^(-10)
    sage: Sq(2,4)*g == u^4
    True
    sage: sorted(list(X.graded_basis(tmin=-15,tmax=-5)))
    [u^(-10), u^(-9), u^(-8), u^(-7), u^(-6), u^(-5)]

Projective spaces, like all modules, can be suspended::

    sage: Q = suspension(QuaternionicProjectiveSpace(),s=5) ; Q
    suspension (0,0,5) of mod 2 cohomology of quaternionic projective space P^{+Infinity}
    sage: Q.an_element()
    (x + x^3 + x^32)*S(0,0,5)


The generators of a suspension lie in the unsuspended module::

    sage: Q.inject_variables()
    Defining x
    sage: x in Q, x in QuaternionicProjectiveSpace()
    (False, True)
    sage: Q.an_element() == (x + x^3 + x^32).suspend(s=5)
    True

Tensor products can be formed::

    sage: M=RealProjectiveSpace(botexp=0)
    sage: N=tensor((M,M))
    sage: sorted(N.graded_basis(t=1))
    [x^0 # x, x # x^0]
    sage: tc=N.tensor_constructor((M,M))
    sage: X = tensor((M.an_element(),M.an_element())) ; X
    x # x + x # x^3 + x # x^32 + x^3 # x + x^3 # x^3 + x^3 # x^32 + x^32 # x + x^32 # x^3 + x^32 # x^32
    sage: Sq(3)*X
    x # x^6 + x^2 # x^5 + x^3 # x^6 + x^4 # x^5 + x^5 # x^2 + x^5 # x^4 + x^6 # x + x^6 # x^3 + x^6 # x^32 + x^32 # x^6
    sage: M.inject_variables()
    Defining x
    sage: X * tensor((x,M.one()))
    x^2 # x + x^2 # x^3 + x^2 # x^32 + x^4 # x + x^4 # x^3 + x^4 # x^32 + x^33 # x + x^33 # x^3 + x^33 # x^32
    sage: tensor((x,M.one())) * tensor((x,M.one()))
    x^2 # x^0

Truncation of tensor products works::

    sage: from yacop.categories.functors import truncation
    sage: M=RealProjectiveSpace()
    sage: N=ComplexProjectiveSpace()
    sage: X=tensor((M,N)) ; X
    mod 2 cohomology of real projective space P^{+Infinity} # mod 2 cohomology of complex projective space P^{+Infinity}
    sage: T=truncation(X,tmax=5)
    sage: sorted(T.graded_basis())
    [x # x, x # x^2, x^2 # x, x^3 # x]
    sage: T.dimension()
    4

CLASS DOCUMENTATION:
"""

# *****************************************************************************
#       Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#  Distributed under the terms of the GNU General Public License (GPL)
# *****************************************************************************

from yacop.utils.region import region
from yacop.modules.module_base import SteenrodModuleBase
from yacop.categories import YacopLeftModuleAlgebras
from sage.rings.infinity import Infinity
from sage.sets.set import Set
from sage.sets.integer_range import IntegerRange
from sage.algebras.all import SteenrodAlgebra
from sage.rings.integer import Integer
from sage.structure.unique_representation import UniqueRepresentation
from yacop.utils.finite_graded_set import InfiniteGradedSet

r"""

  Pickling hack::

    sage: import __main__
    sage: from yacop.modules.projective_spaces import *
    sage: __main__.GenericProjectiveSpace = GenericProjectiveSpace

  TESTS::

        sage: from yacop.modules.projective_spaces import *
        sage: TestSuite(RealProjectiveSpace()).run()
        sage: TestSuite(ComplexProjectiveSpace()).run()
        sage: TestSuite(QuaternionicProjectiveSpace()).run()
        sage: TestSuite(OctonionicProjectiveSpace()).run()

        sage: for cls in [RealProjectiveSpace,ComplexProjectiveSpace,QuaternionicProjectiveSpace,OctonionicProjectiveSpace]:
        ....:       X = cls()
        ....:       x = X.monomial(1)
        ....:       print(x.t,x.e,x.s)
        1 0 0
        2 0 0
        4 0 0
        8 0 0

        sage: # more complicated tests that failed at some point:
        sage: from yacop import *
        sage: X = suspension(RealProjectiveSpace(),s=3)
        sage: TestSuite(X).run()
        sage: Y = suspension(ComplexProjectiveSpace(),t=4)
        sage: Z = cartesian_product((X,Y))
        sage: TestSuite(Z).run()
        sage: M=RealProjectiveSpace(5)
        sage: TestSuite(M).run()

        sage: from yacop.modules.projective_spaces import RealProjectiveSpace
        sage: from yacop.utils.region import region
        sage: P=RealProjectiveSpace()
        sage: P._manual_test_left_action(region(tmax=13))
        131 non-zero multiplications checked
        sage: P._manual_test_left_conj_action(region(tmax=13))
        141 non-zero multiplications checked

        sage: from yacop.modules.projective_spaces import RealProjectiveSpace
        sage: from yacop.categories.functors import truncation
        sage: truncation(RealProjectiveSpace(),tmin=5,tmax=17) is RealProjectiveSpace(botexp=5,topexp=17)

"""


class ProjectiveSpaceBasis(InfiniteGradedSet, UniqueRepresentation):
    def __init__(self, module):
        InfiniteGradedSet.__init__(self, module._top < Infinity)
        self._field = module._field
        self._bot = module._bot
        self._top = module._top

    def bbox(self):
        return region(
            s=0, e=0, tmin=self._field * self._bot, tmax=self._field * self._top
        )

    def degree(self, elem):
        return region(s=0, e=0, t=self._field * elem)

    def _repr_(self):
        return "ProjectiveSpaceBasis (field,bot,top) = (%s,%s,%s)" % (
            self._field,
            self._bot,
            self._top,
        )

    def _truncate_region(self, reg):
        from copy import copy

        reg = copy(reg)
        reg = reg.intersect(self.bbox())
        emin, emax = reg.erange
        smin, smax = reg.srange
        tmin, tmax = reg.trange
        if smax < 0 or smin > 0 or emax < 0 or emin > 0 or tmin > tmax:
            return Set(())
        tmin = max((tmin + self._field - 1) // self._field, self._bot)
        if tmax < Infinity:
            tmax = min(self._top, tmax // self._field)
        else:
            tmax = self._top
        if tmax < Infinity:
            tmax = Integer(tmax + 1)
        return IntegerRange(Integer(tmin), tmax)


class GenericProjectiveSpace(SteenrodModuleBase):
    """
    Cohomology of kP^n for k one of R, C, or O as a module
    over the 2-primary Steenrod algebra.

    TESTS::

        sage: from yacop.modules.projective_spaces import *
        sage: TestSuite(RealProjectiveSpace()).run()
    """

    @staticmethod
    def __classcall_private__(cls, fielddim, topexp=None, botexp=None, prefix=None):
        if topexp is None:
            topexp = +Infinity
        if botexp is None:
            botexp = 0
        if prefix is None:
            prefix = "x"
        return super(GenericProjectiveSpace, cls).__classcall__(
            cls, fielddim, topexp, botexp, prefix
        )

    def __init__(self, fielddim, topexp, botexp, prefix, category=None):
        """
        mod 2 cohomology of kP^topexp/kP^{botexp-1} where dim_R k = fielddim
        """
        self._prime = 2
        self._bot = botexp
        self._top = topexp
        self._field = fielddim
        self._prefix = prefix
        if self._top < Infinity:
            n = Set(list(range(self._bot, self._top)))
        else:
            n = IntegerRange(Integer(self._bot), self._top)

        if category is None:
            category = YacopLeftModuleAlgebras(SteenrodAlgebra(self._prime))
        SteenrodModuleBase.__init__(self, ProjectiveSpaceBasis(self), category=category)

    def _repr_(self):
        fld = "divalg(%d)" % self._field
        if self._field == 1:
            fld = "real"
        if self._field == 2:
            fld = "complex"
        if self._field == 4:
            fld = "quaternionic"
        if self._field == 8:
            fld = "octonionic"
        trunc = ""
        if self._bot != 1:
            trunc = "_{%d}" % (self._bot)
        return "mod 2 cohomology of %s projective space P^{%s}%s" % (
            fld,
            self._top,
            trunc,
        )

    def _repr_term(self, exp):
        letter = self._prefix
        if exp > 1 or exp == 0:
            return "%s^%d" % (letter, exp)
        elif exp < 0:
            return "%s^(%d)" % (letter, exp)
        return letter

    def _latex_term(self, exp):
        letter = self._prefix
        if exp != 1:
            return "%s^{%d}" % (letter, exp)
        return letter

    def an_element(self):
        ans = [self.monomial(u) for u in (1, 3, 32) if u < self._top]
        if 0 == len(ans):
            ans = [self.monomial(self._bot) for u in (0, 2, 7, 15) if self._bot + u <= self._top]
        return self.sum(ans)

    def one_basis(self):
        return 0

    def variable_names(self):
        return (self._prefix,)

    def gens(self):
        return (self.monomial(1),)

    def product_on_basis(self, left, right):
        cf = 1
        s = left + right
        if s > self._top:
            cf = 0
        if s < self._bot:
            raise ValueError("product out of parent")
        return self.linear_combination(((self.monomial(left + right), cf),))

    def left_steenrod_action_milnor(self, a, m):
        sum = 0
        deg = m
        exp = 2
        for i in a:
            if 0 != (i % self._field):
                return self.zero()
            i = Integer(i / self._field)
            if 0 != (sum & i) or deg > self._top:
                return self.zero()
            sum = sum + i
            deg = deg + (exp - 1) * i
            exp = exp * 2
        rest = m - sum
        if 0 != (rest & sum) or deg > self._top:
            return self.zero()
        return self.monomial(deg)

    def left_steenrod_action_milnor_conj(self, a, m):
        """
        TESTS::

            sage: from yacop.modules.projective_spaces import *
            sage: P=RealProjectiveSpace()
            sage: x, = P.gens()
            sage: for i in range(10):
            ....:     for r1 in range(10):
            ....:         for r2 in range(3):
            ....:             assert Sq(r1,r2).antipode() * (x**i) == Sq(r1,r2) % (x**i)
        """
        sum = 0
        deg = m
        exp = 2
        psum = 0
        for i in a:
            if 0 != (i % self._field):
                return self.zero()
            i = Integer(i / self._field)
            if 0 != (sum & i) or deg > self._top:
                return self.zero()
            sum = sum + i
            deg = deg + (exp - 1) * i
            psum = psum + exp * i
            exp = exp * 2
        rest = -1 - m - psum
        if 0 != (rest & sum) or deg > self._top:
            return self.zero()
        return self.monomial(deg)

    def TruncatedObjectsFactory(self,module,*args,**kwargs):
        reg = region(**kwargs)
        topexp = min(reg.tmax,self._top)
        botexp = max(reg.tmin,self._bot)
        fielddim = self._field
        prefix = self._prefix
        return GenericProjectiveSpace(fielddim, topexp, botexp, prefix)


def RealProjectiveSpace(topexp=+Infinity, botexp=1, prefix="x", **args):
    """
    Cohomology of a real projective space P^n or a truncation P^n_k.

     EXAMPLE::

         sage: from yacop.modules.projective_spaces import *
         sage: RealProjectiveSpace()
         mod 2 cohomology of real projective space P^{+Infinity}
         sage: RealProjectiveSpace(7,botexp=3,prefix="u")
         mod 2 cohomology of real projective space P^{7}_{3}
    """
    return GenericProjectiveSpace(1, topexp, botexp=botexp, prefix=prefix, **args)


def ComplexProjectiveSpace(topexp=+Infinity, botexp=1, prefix="x", **args):
    """
    Cohomology of a complex projective space P^n or a truncation P^n_k.

     EXAMPLE::

         sage: from yacop.modules.projective_spaces import *
         sage: ComplexProjectiveSpace()
         mod 2 cohomology of complex projective space P^{+Infinity}
         sage: ComplexProjectiveSpace(7,botexp=3,prefix="u")
         mod 2 cohomology of complex projective space P^{7}_{3}
    """
    return GenericProjectiveSpace(2, topexp, botexp=botexp, prefix=prefix, **args)


def QuaternionicProjectiveSpace(topexp=+Infinity, botexp=1, prefix="x", **args):
    """
    Cohomology of a quaternionic projective space P^n or a truncation P^n_k.

     EXAMPLE::

         sage: from yacop.modules.projective_spaces import *
         sage: QuaternionicProjectiveSpace()
         mod 2 cohomology of quaternionic projective space P^{+Infinity}
         sage: QuaternionicProjectiveSpace(7,botexp=3,prefix="u")
         mod 2 cohomology of quaternionic projective space P^{7}_{3}
    """
    return GenericProjectiveSpace(4, topexp, botexp=botexp, prefix=prefix, **args)


def OctonionicProjectiveSpace(topexp=+Infinity, botexp=1, prefix="x", **args):
    """
    Cohomology of a octonionic projective space P^n or a truncation P^n_k.

     EXAMPLE::

         sage: from yacop.modules.projective_spaces import *
         sage: OctonionicProjectiveSpace()
         mod 2 cohomology of octonionic projective space P^{+Infinity}
         sage: OctonionicProjectiveSpace(7,botexp=3,prefix="u")
         mod 2 cohomology of octonionic projective space P^{7}_{3}
    """
    return GenericProjectiveSpace(8, topexp, botexp=botexp, prefix=prefix, **args)


# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

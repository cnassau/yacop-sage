r"""
A base class for Steenrod algebra modules.

AUTHORS: - Christian Nassau (2011-05-13: version 1.0)

CLASS DOCUMENTATION:
"""

# *****************************************************************************
#       Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#  Distributed under the terms of the GNU General Public License (GPL)
# *****************************************************************************

from yacop.utils.region import region
from yacop.utils.gradings import YacopGrading
from yacop.utils.set_of_elements import SetOfMonomials
from yacop.modules.module_base import SteenrodModuleBase
from yacop.categories import YacopLeftModuleAlgebras, YacopGradedObjects
from yacop.categories.functors import suspension, SuspendedObjectsCategory
from yacop.categories.functors import truncation, TruncatedObjectsCategory
from sage.rings.infinity import Infinity
from sage.combinat.free_module import CombinatorialFreeModule
from sage.structure.sage_object import SageObject
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.sets.set import Set
from sage.sets.family import LazyFamily
from sage.categories.examples.infinite_enumerated_sets import NonNegativeIntegers
from sage.categories.algebras_with_basis import AlgebrasWithBasis
from sage.categories.enumerated_sets import EnumeratedSets
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.sets.integer_range import IntegerRange
from sage.algebras.all import SteenrodAlgebra, Sq
from sage.rings.integer import Integer
from sage.structure.formal_sum import FormalSum, FormalSums
from sage.structure.unique_representation import UniqueRepresentation
from sage.misc.cachefunc import cached_method
from sage.arith.misc import binomial
from sage.misc.lazy_format import LazyFormat
from sage.categories.sets_cat import Sets
from sage.categories.morphism import SetMorphism

class MorphModule(SteenrodModuleBase):
    """
    Common base class for kernels, images and cokers.

    A ``MorphModule`` knows about a morphism ``f`` and an ambient space ``A``.

        =============================
        | Module    | ambient Space |
        -----------------------------
        | kernel(f) | f.domain()    |
        | image(f)  | f.codomain()  |
        | coker(f)  | f.codomain()  |
        =============================

    The keys of a ``MorphModule`` are pairs ``(region,idx)``. Elements
    are printed through their lifts in the ambient space.

    A ``MorphModule`` expects these abstract methods
    """

    def __init__(self, f, ambient, category=None, truncate_to=None):
        self._f = f
        self._am = ambient
        if category is None:
            C = f.domain().category()
            category = C.Subquotients()
        else:
            category = category.Subquotients()
        gr = self._am.grading().SubquotientGrading(self)

        if not truncate_to is None:
            gr = truncation(gr, **truncate_to.as_dict())

        if gr.bbox().is_finite("t", "e", "s") or ambient.basis().is_finite():
            self._card = -1
            # finite but unknown
        else:
            self._card = Infinity

        self.__bklist = None

        from sage.sets.family import Family

        keys = Family(
            IntegerRange(Integer(0), +Infinity),
            lambda i: self.__basis_key_by_idx(i),
            lazy=True,
        )
        import types

        def contains(fam, x):
            try:
                reg, idx = x
            except:
                return False
            return x in self._compute_basis_keys(reg)

        keys.__contains__ = types.MethodType(contains, keys)
        SteenrodModuleBase.__init__(self, keys, grading=gr, category=category)

        if True:
            # fix various basis issues
            b = self.basis()
            b.rename(
                "<<private and inefficient basis family: use graded_basis instead>>"
            )
            b.max_test_enumerated_set_loop = 5

            def some_elements(fam):
                from itertools import islice

                return list(islice(fam, 5))

            b.some_elements = types.MethodType(some_elements, b)
            k = b.keys()
            k.rename("<<private and inefficient key family: don't use this>>")
            k.max_test_enumerated_set_loop = 5

            def some_elements(fam):
                from itertools import islice

                return list(islice(fam, 5))

            k.some_elements = types.MethodType(some_elements, k)
            k._contains_ = types.MethodType(contains, k)

    def an_element(self, region=None, attempts=30):
        """
        Return a representative element of `self`, for testing purposes.
        """
        # we try to return a non-homogeneous element, if possible
        from itertools import islice

        ans = []
        if self.base_ring().characteristic() == 2:
            fac = 1
        else:
            fac = 2
        cf = 1
        for deg in islice(self.nontrivial_degrees(), attempts):
            for bk in self.graded_basis(deg):
                ans.append((bk, cf))
                cf = cf * fac
                break
            if len(ans) > 2:
                break
        if len(ans) == 0:
            raise ValueError("cannot find a nontrivial element")
        return self.linear_combination(ans)

    @cached_method
    def _module_basis(self, region):
        assert (
            region.tmax == region.tmin
            and region.emax == region.emin
            and region.smax == region.smin
        )
        ans = []
        M = self.ambient()
        bas = [t for t in M.graded_basis(region)]
        for vec in self._module(region).basis():
            ans.append(M.linear_combination(list(zip(bas, vec))))
        return ans

    def _compute_basis_keys(self, region=None):
        k = self._module_basis(region)
        return [(k[idx].degree(), idx) for idx in range(0, len(k))]

    def _compute_basis(self, region=None):
        return [self.monomial(g) for g in self._compute_basis_keys(region)]

    def __basis_key_iterator(self, region=None, attempts=+Infinity):
        """
        An iterator that walks through nontrivial bidegrees and their bases.

        Caution: this iterable might be infinite.
        """
        cnt = 0
        for deg in self.nontrivial_degrees(region):
            cnt = cnt + 1
            if cnt > attempts:
                raise ValueError("no basis key found after %s attempts" % attempts)
            for key in self._compute_basis_keys(deg):
                yield key

    def _basis_walker(self, region=None):
        from yacop.utils.walker import Walker

        class momobasis_walker(Walker):
            def __init__(self, morphmod, region, cardhint):
                self.mod = morphmod
                self.reg = region
                self._card = cardhint
                r = self.reg
                if (
                    not r is None
                    and r.tmin == r.tmax
                    and r.emin == r.emax
                    and r.smin == r.smax
                ):
                    cat = FiniteEnumeratedSets()
                else:
                    cat = EnumeratedSets()
                Walker.__init__(self, category=cat)
                self.degiter = self.mod.ambient().nontrivial_degrees(region).__iter__()
                self.xbas = []

            def __iter__(self):
                return momobasis_walker(self.mod, self.reg, self._card)

            def __next__(self):
                if len(self.xbas) > 0:
                    return self.xbas.pop()
                self.xbas = self.mod._compute_basis(next(self.degiter))
                return next(self)

            def _repr_(self):
                return "basis walker in %s of %s" % (self.reg, self.mod)

            @cached_method
            def cardinality(self):
                r = self.reg
                if not r is None and r.is_finite("e", "s", "t"):
                    return len([u for u in self])
                if self._card < Infinity:
                    return len([u for u in self])
                return Infinity

        return momobasis_walker(self, self._am.bbox().intersect(region), self._card)

    def __basis_key_next(self):
        if self.__bklist is None:
            self.__bknum = -1
            self.__bkit = self.__basis_key_iterator()
            self.__bklist = []
        self.__bknum = self.__bknum + 1
        nxt = next(self.__bkit)
        self.__bklist.append(nxt)
        return self.__bknum, nxt

    def __basis_key_by_idx(self, idx, region=None):
        """
        returns the element number idx from self.basis_key_iterator().

        Caution: this routine is very slow and expensive. It's only here
        to support automatic testing of this object type.
        """
        assert idx >= 0
        while self.__bklist is None or len(self.__bklist) <= idx:
            self.__basis_key_next()
        return self.__bklist[idx]

    def _can_test_pickling(self):
        try:
            if self._f == loads(dumps(self._f)):
                return True
        except:
            pass
        return False

    def ambient(self):
        """
        Ambient space as per ``Subquotient`` category.
        """
        return self._am

    def _compute_matrix(self, region):
        from sage.matrix.constructor import matrix

        # this should only ever be called for single bidegrees
        assert (
            region.tmin == region.tmax
            and region.emin == region.emax
            and region.smin == region.smax
        )
        M, N = self._f.domain(), self._f.codomain()
        mt = []
        nrows = 0
        ncols = len(N.graded_basis(region))
        for s in M.graded_basis(region):
            nrows += 1
            d = self._f(s)
            mt.append(N.graded_basis_coefficients(d, region))
        # have to specify the ring and nrows, ncols in order to get the
        # right class and dimensions in case where mt is empty
        return matrix(mt, ring=GF(self._prime), nrows=nrows, ncols=ncols)

    def suspend_element(self, elem, **options):
        sp = suspension(self, **options)
        offset = region(**options)
        ans = [
            ((reg + offset, idx), cf)
            for ((reg, idx), cf) in elem.monomial_coefficients().items()
        ]
        return sp._from_dict(dict(ans))

    if False:
        # hack: in some circumstances an __init_extra__ is invoked
        # before the full list of bases to self has been installed
        # we need dummy wrappers for the functions expected in __init_extra__
        # to cope with this:
        def left_steenrod_action_on_basis(self,*args):
            return super().left_steenrod_action_on_basis(*args)
        def left_conj_steenrod_action_on_basis(self,*args):
            return super().left_conj_steenrod_action_on_basis(*args)
        def right_steenrod_action_on_basis(self,*args):
            return super().right_steenrod_action_on_basis(*args)
        def right_conj_steenrod_action_on_basis(self,*args):
            return super().right_conj_steenrod_action_on_basis(*args)

    class Element(SteenrodModuleBase.Element):
        def _repr_(elem):
            return elem.parent().lift(elem)._repr_()

        def _latex_(elem):
            return elem.parent().lift(elem)._latex_()

        def _can_test_pickling(elem):
            return elem.parent()._can_test_pickling()

        def _test_pickling(self, tester=None, **options):
            if self.parent()._can_test_pickling():
                super(MorphModule.Element, self)._test_pickling(
                    tester=tester, **options
                )


class KernelImpl(MorphModule):
    """
    Implements the kernel of a morphism between Steenrod algebra modules.

    TESTS::

       sage: from yacop.modules.all import RealProjectiveSpace, ComplexProjectiveSpace
       sage: M=RealProjectiveSpace()
       sage: N=ComplexProjectiveSpace()
       sage: X=cartesian_product((M,N))
       sage: f=X.cartesian_projection(0)
       sage: f.rename("the summand projection")
       sage: K = kernel(f)
       sage: print(K)
       kernel of the summand projection
       sage: kernel(f) is kernel(f)
       True
       sage: K.category()
       Category of subquotients of yacop left module algebras over mod 2 Steenrod algebra, milnor basis
       sage: TestSuite(K).run() # long time

    """

    @staticmethod
    def __classcall_private__(cls, f, **options):
        return super(KernelImpl, cls).__classcall__(cls, f, **options)

    def __init__(self, f, **options):
        MorphModule.__init__(self, f, f.domain(), **options)
        f.domain().register_coercion(self.ambient_embedding())

    @cached_method
    def ambient_embedding(self):
        res = self.module_morphism(
            codomain=self._f.domain(), on_basis=lambda i: self.lift(self.monomial(i))
        )
        res.rename("kernel embedding of %s" % self)
        return res

    def _repr_(self):
        return "kernel of %s" % self._f

    def lift(self, elem):
        """
        Lift as per ``Subquotient`` category.
        """
        M = self.ambient()
        ans = []
        for (key, v) in elem.monomial_coefficients().items():
            rg, idx = key
            ans.append((self._module_basis(rg)[idx], v))
        return M.linear_combination(ans)

    def _retract_homogeneous(self, deg, elem):
        """
        Cast an element of ``f.domain()`` into ``kernel(f)``, if possible.
        """
        M = self.ambient()
        vec = M.graded_basis_coefficients(elem, deg)
        k = self._module(deg)
        try:
            kvec = k(vec)
        except:
            if not self._f(elem) == 0:
                raise ValueError("%s is not in kernel" % elem)
            raise ValueError("internal error: cannot cast %s to kernel" % elem)
        coeffs = k.echelon_coordinates(kvec)
        return self.linear_combination(list(zip(self._compute_basis(deg), coeffs)))

    @cached_method
    def _module(self, region=None):
        m = self._compute_matrix(region)
        return m.kernel()

    class Element(MorphModule.Element):
        def _test_element_in_kernel(self, tester=None, **options):
            tester = self._tester(tester=tester, **options)
            tester.assertTrue(
                self.parent()._f(self) == 0,
                LazyFormat("element %s not in kernel") % (self,),
            )

    @cached_method
    def SuspendedObjectsFactory(module, *args, **kwopts):
        # rewrite susp(ker f) as ker(susp f)
        return KernelImpl(suspension(module._f, *args, **kwopts))


class ImageImpl(MorphModule):
    """
    Implements the image of a morphism between Steenrod algebra modules.

    TESTS::

       sage: from yacop.modules.all import RealProjectiveSpace, ComplexProjectiveSpace
       sage: M=RealProjectiveSpace()
       sage: N=ComplexProjectiveSpace()
       sage: X=cartesian_product((M,N))
       sage: f=X.summand_embedding(1)
       sage: f.rename("the summand inclusion")
       sage: I = image(f)
       sage: print(I)
       image of the summand inclusion
       sage: image(f) is image(f)
       True
       sage: i=I.an_element() ; i
       (0, x + x^2 + x^3)
       sage: I.lift(i)
       (0, x + x^2 + x^3)
       sage: i == I.retract(I.lift(i))
       True
       sage: n = N.an_element() ; n
       x + x^3 + x^32
       sage: n2 = I.retract(f(n)) ; n2
       (0, x + x^3 + x^32)
       sage: f(n) == I.lift(n2)
       True
       sage: n == I.preimage(n2)
       True
       sage: I.category()
       Category of subquotients of yacop left module algebras over mod 2 Steenrod algebra, milnor basis
       sage: TestSuite(I).run()  # long time

    """

    @staticmethod
    def __classcall_private__(cls, f, **options):
        return super(ImageImpl, cls).__classcall__(cls, f, **options)

    def __init__(self, f, **options):
        bbox = f.domain().bbox().intersect(f.codomain().bbox())
        MorphModule.__init__(self, f, f.codomain(), truncate_to=bbox, **options)
        self.ambient().register_coercion(self.ambient_embedding())
        # TODO: implement printing by pre-images

    @cached_method
    def ambient_embedding(self):
        res = self.module_morphism(
            codomain=self._f.codomain(), on_basis=lambda i: self.lift(self.monomial(i))
        )
        res.rename("image embedding of %s" % self)
        return res

    def _convert_map_from_(self, S):
        if S is self.ambient():
            return SetMorphism(S.Hom(self, category=Sets()),
                               lambda x: self.retract(x))

        return super()._convert_map_from_(S)

    def _repr_(self):
        return "image of %s" % self._f

    def lift(self, elem):
        """
        Lift as per ``Subquotient`` category. This does nothing for elements of image(f).
        """
        M = self.ambient()
        ans = []
        for (key, v) in elem.monomial_coefficients().items():
            rg, idx = key
            ans.append((self._module_basis(rg)[idx], v))
        return M.linear_combination(ans)

    def _retract_homogeneous(self, deg, elem):
        """
        Cast an element of ``f.codomain()`` into ``image(f)``, if possible.
        """
        M = self.ambient()
        vec = M.graded_basis_coefficients(elem, deg)
        k = self._module(deg)
        try:
            kvec = k(vec)
        except:
            if not self._f(elem) == 0:
                raise ValueError("%s is not in kernel" % elem)
            raise ValueError("internal error: cannot cast %s to kernel" % elem)
        coeffs = k.echelon_coordinates(kvec)
        return self.linear_combination(list(zip(self._compute_basis(deg), coeffs)))

    @cached_method
    def _module(self, region=None):
        m = self._compute_matrix(region)
        return m.image()

    @cached_method
    def _preimages(self, region):
        from sage.matrix.constructor import matrix

        m = self._compute_matrix(region).transpose()
        M = self._f.domain()
        b = M.graded_basis(region)
        Z = matrix(self._module(region).basis()).transpose()
        s = m.solve_right(Z)
        ans = []
        for vec in s.columns():
            ans.append(M.linear_combination(list(zip(b, vec))))
        return ans

    def preimage(self, elem):
        ans = []
        M = self._f.domain()
        for (k, v) in elem.monomial_coefficients().items():
            reg, idx = k
            ans.append((self._preimages(reg)[idx], v))
        return M.linear_combination(ans)

    class Element(MorphModule.Element):
        def preimage(self):
            return self.parent().preimage(self)

    @cached_method
    def SuspendedObjectsFactory(module, *args, **kwopts):
        # rewrite susp(im f) as im(susp f)
        return ImageImpl(suspension(module._f, *args, **kwopts))


class SubModule(ImageImpl):
    """
    The submodule over the Steenrod algebra generated by some subset.

    .. warning:: currently only left modules are implemented.

    TESTS::

        sage: from yacop.modules.free_modules import YacopFreeModule
        sage: from yacop.modules.morph_module import SubModule as YacopSubModule
        sage: A = SteenrodAlgebra(5)
        sage: P,Q = A.P, A.Q_exp
        sage: F.<a,b> = YacopFreeModule(A,('a','b'))
        sage: S = YacopSubModule(F,(P(6)*a+3*P(0,1)*b,P(7)*a)) ; S
        submodule of free module over mod 5 Steenrod algebra, milnor basis on [a, b] generated by (3*P(0,1)*b + P(6)*a, P(7)*a)
        sage: for dim in (0,..,85):
        ....:     lst = sorted(list(S.graded_basis(t=dim)))
        ....:     if len(lst)>0:
        ....:        print("%3d"%dim,":",sorted(list(S.graded_basis(t=dim))))
        48 : [3*P(0,1)*b + P(6)*a]
        49 : [3*Q_0 P(0,1)*b + Q_0 P(6)*a]
        56 : [P(7)*a, P(1,1)*b]
        57 : [3*Q_1 P(0,1)*b + Q_1 P(6)*a, Q_0 P(7)*a, Q_0 P(1,1)*b]
        58 : [3*Q_0 Q_1 P(0,1)*b + Q_0 Q_1 P(6)*a]
        64 : [P(8)*a, P(2,1)*b]
        65 : [Q_1 P(7)*a, Q_0 P(8)*a, Q_1 P(1,1)*b, Q_0 P(2,1)*b]
        66 : [Q_0 Q_1 P(7)*a, Q_0 Q_1 P(1,1)*b]
        72 : [P(9)*a, P(3,1)*b]
        73 : [Q_1 P(8)*a, Q_0 P(9)*a, Q_1 P(2,1)*b, Q_0 P(3,1)*b]
        74 : [Q_0 Q_1 P(8)*a, Q_0 Q_1 P(2,1)*b]
        80 : [P(4,1)*b]
        81 : [Q_1 P(9)*a, Q_1 P(3,1)*b, Q_0 P(4,1)*b]
        82 : [Q_0 Q_1 P(9)*a, Q_0 Q_1 P(3,1)*b]
        sage: S.category()
        Category of subquotients of yacop left modules over mod 5 Steenrod algebra, milnor basis
        sage: TestSuite(S).run()

        sage: from yacop.modules.all import DualSteenrodAlgebra
        sage: D=DualSteenrodAlgebra(2,generic=True)
        sage: xi,tau=D.gens()
        sage: M=YacopSubModule(D,(tau[0]*tau[1],)) ; M
        submodule of generic dual Steenrod algebra at the prime 2 generated by (tau[0]*tau[1],)
        sage: sorted(M.graded_basis())
        [tau[0]*tau[1], tau[1] + tau[0]*xi[1], tau[0], 1]

    """

    def __init__(self, ambient, generators, category=None):
        from yacop.modules.free_modules import YacopFreeModule
        self._generators = tuple([ambient(_) for _ in generators])
        A = ambient._yacop_base_ring
        F = YacopFreeModule(A, generators, tesfunc=lambda x: (x.t, x.e, x.s))
        f = F.left_linear_morphism(codomain=ambient, on_basis=lambda x:x)
        ImageImpl.__init__(self, f, category=category)

    def _repr_(self):
        return "submodule of %s generated by %s" % (self.ambient(), self._generators)


class CokerImpl(MorphModule):
    """
    Implements the cokernel of a morphism between Steenrod algebra modules.

    TESTS::

       sage: from yacop.utils.region import region
       sage: from yacop.modules.all import BZp
       sage: from yacop import cokernel
       sage: M=BZp(7)
       sage: X=cartesian_product((M,M))
       sage: emb1 = X.summand_embedding(0)
       sage: emb2 = X.summand_embedding(1)
       sage: f=M.module_morphism(codomain=X,on_basis=lambda i:2*emb1(M.monomial(i))+emb2(M.monomial(i)))
       sage: f.rename("2*iota_1 + iota_2")
       sage: C = cokernel(f)
       sage: print(C)
       cokernel of 2*iota_1 + iota_2
       sage: cokernel(f) is cokernel(f)
       True
       sage: c=C.an_element() ; c
       (1 + 2*y + 4*x, 0)
       sage: cl = C.lift(c) ; cl
       (1 + 2*y + 4*x, 0)
       sage: C.retract(cl) == c
       True
       sage: C.retract(cl+f(M.an_element())) == c
       True
       sage: M.an_element()
       y + 3*x^2 + 2*y*x^5 + 5*x^17
       sage: C(X.summand_embedding(0)(M.an_element()))
       (y + 3*x^2 + 2*y*x^5 + 5*x^17, 0)
       sage: C(X.summand_embedding(1)(M.an_element()))
       (5*y + x^2 + 3*y*x^5 + 4*x^17, 0)
       sage: b = C.graded_basis(region(tmax=10))
       sage: sorted(b) # random order
       [(1, 0), (x, 0), (x^2, 0), (x^3, 0), (x^4, 0), (x^5, 0), (y, 0), (y*x, 0), (y*x^2, 0), (y*x^3, 0), (y*x^4, 0)]
       sage: len(b)
       11
       sage: C.category()
       Category of subquotients of yacop left module algebras over mod 7 Steenrod algebra, milnor basis
       sage: TestSuite(C).run()  # long time

    """

    @staticmethod
    def __classcall_private__(cls, f, **options):
        return super(CokerImpl, cls).__classcall__(cls, f, **options)

    def __init__(self, f, **options):
        MorphModule.__init__(self, f, f.codomain(), **options)
        self.register_coercion(self.retraction_morphism())

    @cached_method
    def retraction_morphism(self):
        M = self._f.codomain()
        res = M.module_morphism(
            codomain=self, on_basis=lambda i: self.retract(M.monomial(i))
        )
        res.rename("cokernel projection of %s" % self)
        return res

    def _repr_(self):
        return "cokernel of %s" % self._f

    def lift(self, elem):
        """
        Lift as per ``Subquotient`` category. For ``cokernel(f)`` this returns a
        representative of ``elem`` in ``f.domain()``.
        """
        M = self.ambient()
        ans = []
        for (key, v) in elem.monomial_coefficients().items():
            rg, idx = key
            ans.append((self._module_basis(rg)[idx], v))
        return M.linear_combination(ans)

    def _retract_homogeneous(self, deg, elem):
        """
        Project an element of ``f.codomain()`` into ``cokernel(f)``.
        """
        M = self.ambient()
        vec = M.graded_basis_coefficients(elem, deg)
        k = self._module(deg)
        try:
            kvec = k(vec)
        except:
            if not self._f(elem) == 0:
                raise ValueError("%s is not in kernel" % elem)
            raise ValueError("internal error: cannot cast %s to kernel" % elem)
        coeffs = k.echelon_coordinates(kvec)
        return self.linear_combination(list(zip(self._compute_basis(deg), coeffs)))

    @cached_method
    def _module(self, region=None):
        m = self._compute_matrix(region)
        I = m.image()
        return I.ambient_module().quotient(I)

    @cached_method
    def _module_basis(self, region):
        assert (
            region.tmax == region.tmin
            and region.emax == region.emin
            and region.smax == region.smin
        )
        ans = []
        M = self.ambient()
        bas = [t for t in M.graded_basis(region)]
        sm = self._module(region)
        lmap = sm.lift_map()
        for vec in sm.basis():
            v = lmap(vec)
            ans.append(M.linear_combination(list(zip(bas, v))))
        return ans

    @cached_method
    def _preimages(self, region):
        from sage.matrix.constructor import matrix

        m = self._compute_matrix(region).transpose()
        M = self._f.domain()
        b = M.graded_basis(region)
        Z = matrix(self._module(region).basis()).transpose()
        s = m.solve_right(Z)
        ans = []
        for vec in s.columns():
            ans.append(M.linear_combination(list(zip(b, vec))))
        return ans

    def preimage(self, elem):
        ans = []
        M = self._f.domain()
        for (k, v) in elem.monomial_coefficients().items():
            reg, idx = k
            ans.append((self._preimages(reg)[idx], v))
        return M.linear_combination(ans)

    class Element(MorphModule.Element):
        def _xxxtest_element_in_kernel(self, tester=None, **options):
            tester = self._tester(tester=tester, **options)
            tester.assertTrue(
                self.parent()._f(self) == 0,
                LazyFormat("element %s not in kernel") % (self,),
            )

    @cached_method
    def SuspendedObjectsFactory(module, *args, **kwopts):
        # rewrite susp(coker f) as coker(susp f)
        return CokerImpl(suspension(module._f, *args, **kwopts))


# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

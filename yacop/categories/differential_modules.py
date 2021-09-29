r"""
The Yacop category for differential modules.
"""
# *****************************************************************************
#  Copyright (C) 2011-      Christian Nassau <nassau@nullhomotopie.de>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
# ******************************************************************************
# pylint: disable=E0213

from sage.rings.infinity import Infinity
from sage.misc.abstract_method import abstract_method
from sage.misc.cachefunc import cached_method
from sage.misc.lazy_attribute import lazy_attribute
from sage.categories.category_singleton import Category_singleton
from sage.categories.category_types import Category_over_base_ring
from sage.categories.homsets import HomsetsCategory
from sage.categories.all import (
    Category,
    Sets,
    Hom,
    Rings,
    Modules,
    LeftModules,
    RightModules,
    Bimodules,
    ModulesWithBasis,
    AlgebrasWithBasis,
)
from sage.categories.objects import Objects
from sage.categories.cartesian_product import (
    CartesianProductsCategory,
    cartesian_product,
)
from sage.categories.subquotients import SubquotientsCategory
from sage.categories.algebra_functor import AlgebrasCategory
from sage.categories.dual import DualObjectsCategory
from sage.categories.tensor import TensorProductsCategory, tensor
from sage.categories.morphism import SetMorphism
from sage.misc.cachefunc import cached_method
from sage.structure.sage_object import SageObject
from sage.structure.element import have_same_parent
from yacop.utils.region import region
from yacop.categories.functors import SuspendedObjectsCategory
from yacop.categories.functors import TruncatedObjectsCategory
from sage.misc.cachefunc import cached_function
from sage.misc.classcall_metaclass import typecall, ClasscallMetaclass
from yacop.categories.functors import suspension
from sage.misc.lazy_attribute import lazy_attribute
from sage.rings.all import GF
from sage.categories.homset import Homset
from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra

from yacop.categories.graded_objects import YacopGradedObjects


class YacopDifferentialModules(Category_over_base_ring):
    """
    The category of differential Yacop modules over the Steenrod algebra.

    EXAMPLES::

        sage: from yacop.categories import *
        sage: YacopDifferentialModules(SteenrodAlgebra(7))
        Category of yacop differential modules over mod 7 Steenrod algebra, milnor basis
    """

    def __init__(self, R):
        Category_over_base_ring.__init__(self, R)

    def an_instance(self):
        """
        EXAMPLE::

            sage: from yacop.categories import *
            sage: YacopLeftModules(SteenrodAlgebra(2)).an_instance()
            mod 2 cohomology of real projective space P^{+Infinity}
            sage: YacopLeftModules(SteenrodAlgebra(5)).an_instance()
            mod 5 cohomology of the classifying space of ZZ/5ZZ
        """
        from yacop.modules.all import RealProjectiveSpace, BZp

        if self.base_ring().is_generic():
            return BZp(self.base_ring().characteristic())
        else:
            return RealProjectiveSpace()

    def _repr_object_names(self):
        return "yacop differential modules over %s" % self.base_ring()

    def ModuleCategory(self):
        return self

    @cached_method
    def super_categories(self):
        """
        TESTS::

            sage: from yacop.categories import *
            sage: YacopDifferentialModules(SteenrodAlgebra(2)).super_categories()
            [Category of vector spaces with basis over Finite Field of size 2,
             Category of yacop graded objects]

        """
        from sage.categories.modules_with_basis import ModulesWithBasis

        R = self.base_ring()
        x = []
        x.append(ModulesWithBasis(R.base_ring()))
        x.append(YacopGradedObjects())
        return x

    class ParentMethods:
        @cached_method
        def __xxyacop_category__(self):
            for cat in self.categories():
                if hasattr(cat, "_is_yacop_module_category"):
                    if cat._is_yacop_module_category:
                        return cat
            raise ValueError("internal error: cannot detect yacop category")


        def _Hom_(X, Y, category):
            # here we overwrite the Rings._Hom_ implementation
            return Homset(X, Y, category=category)

        def module_morphism(self, *args, **kwargs):
            """
            TESTS::

                sage: from yacop.categories import *
                sage: from yacop.modules.all import RealProjectiveSpace
                sage: M = RealProjectiveSpace()
                sage: X = cartesian_product((M,M))
                sage: f = X.cartesian_projection(0)
                sage: C = YacopLeftModules(SteenrodAlgebra(2))
                sage: f in C.Homsets() # random, works in sage shell
                True
                sage: hasattr(f,"kernel") # indirect test that f is in the Homsets category
                True

            """
            # hack to fix the automatic category detection
            Y = self.__yacop_category__()
            cat = kwargs.pop("category", Y)
            codomain = kwargs.pop("codomain", self)
            cat = cat.category().meet((self.category(), codomain.category()))
            kwargs["category"] = cat
            kwargs["codomain"] = codomain
            ans = ModulesWithBasis(Y.base_ring().base_ring()).parent_class.module_morphism(
                self, *args, **kwargs
            )
            # there is a known issue with morphism categories (see sage code)
            # disable the _test_category and _test_pickling method for this instance:

            def dummy(*args, **kwopts):
                pass

            setattr(ans, "_test_category", dummy)
            setattr(ans, "_test_pickling", dummy)
            return ans

        # some routines (for example the combinatorial free modules' cartesian_product
        # cartesian_projection) use the underscored version instead
        _module_morphism = module_morphism

        def KernelOf(self, f, **options):
            """
            create the kernel of the map ``f``. ``domain(f)`` must be self.
            """
            from yacop.modules.morph_module import KernelImpl

            assert f.domain() is self
            return KernelImpl(f, **options)

        def ImageOf(self, f, **options):
            """
            create the image of the map ``f`` ``domain(f)`` must be self.
            """
            from yacop.modules.morph_module import ImageImpl

            assert f.codomain() is self
            return ImageImpl(f, **options)

        def CokernelOf(self, f, **options):
            """
            create the cokernel of the map ``f`` ``domain(f)`` must be self.
            """
            from yacop.modules.morph_module import CokerImpl

            assert f.codomain() is self
            return CokerImpl(f, **options)

        def differential(self, elem):
            return self.differential_morphism()(elem)

        def differential_morphism(self):
            try:
                if not self._differential_dict is None:
                    return self._differential_morphism_from_dict
            except AttributeError:
                pass
            return self._differential_morphism_from_basis

        _differential_dict = None

        def differential_reset(self):
            self._differential_dict = None

        def differential_clear(self):
            self._differential_dict = {}

        def differential_set(self, lst):
            if self._differential_dict is None:
                self.differential_clear()
            for (elem, dst) in lst:
                if len(elem) != 1:
                    raise ValueError("source element must be a monomial")
                ((key, cf),) = elem
                self._differential_dict[key] = (1 / cf) * dst

        @lazy_attribute
        def _differential_morphism_from_dict(self):
            ans = self.module_morphism(
                codomain=self, on_basis=self._differential_from_dict
            )
            ans.rename("internal differential of %s" % self)
            return ans

        @lazy_attribute
        def _differential_morphism_from_basis(self):
            ans = self.module_morphism(
                codomain=self, on_basis=self._differential_on_basis
            )
            ans.rename("internal differential of %s" % self)
            return ans

        def _differential_on_basis(self, key):
            """
            default differential is zero
            """
            return self.zero()

        def _differential_from_dict(self, key):
            try:
                return self._differential_dict[key]
            except KeyError:
                return self.zero()

        def _xx_test_truncation(self, tester=None, **options):
            from yacop.categories.functors import truncation
            from sage.misc.sage_unittest import TestSuite
            from sage.misc.lazy_format import LazyFormat

            is_sub_testsuite = tester is not None
            tester = self._tester(tester=tester, **options)
            myatt = "_truncation_tested"
            if not hasattr(self, myatt):
                # find a non-zero action a*m = n in self
                def testops(A):
                    for _ in A.some_elements():
                        yield _
                    maxdeg = A.prime() ** 3
                    for deg in range(1, maxdeg):
                        for key in A.homogeneous_component(maxdeg - deg + 1).basis():
                            yield A(key)

                n = self.zero()
                for (deg, m) in list(
                    self.an_element().homogeneous_decomposition().items()
                ):
                    if not m.is_zero():
                        for a in testops(self._yacop_base_ring):
                            n = a * m
                            # print("trying %s*%s->%s"%(a,m,n))
                            if not n.is_zero():
                                break
                        if not n.is_zero():
                            break
                if n.is_zero() or m.t == n.t:
                    print(("WARN: could not find a non-trivial action in %s" % self))
                else:
                    tests = []
                    # tests are tuples:
                    #   1 region to truncate to
                    #  flags whether
                    #   2 m survives to truncation
                    #   3 n survives to truncation
                    #  and
                    #   4 result of computing a*m in the truncation
                    tests.append(((m.t, n.t), True, True, n))
                    tests.append(((m.t, m.t), True, False, 0))
                    tests.append(((n.t, n.t), False, True, 0))
                    for ((tmin, tmax), sm, sn, am) in tests:
                        T = truncation(self, tmin=tmin, tmax=tmax)
                        if sm:
                            tester.assertTrue(
                                m in T,
                                LazyFormat("contains (+) broken for %s (elem %s)")
                                % (T, n),
                            )
                            tester.assertTrue(
                                self(T(m)) == m,
                                LazyFormat(
                                    "casting from/to truncation broken for %s (elem %s)"
                                )
                                % (T, n),
                            )
                            tester.assertTrue(
                                T(m).parent() is T,
                                LazyFormat("wrong parent for %s (elem %s)") % (T, n),
                            )
                        else:
                            tester.assertTrue(
                                not m in T,
                                LazyFormat("contains (-) broken for %s (elem %s)")
                                % (T, n),
                            )
                            ok = False
                            try:
                                x = T(m)
                            except:
                                ok = True
                            tester.assertTrue(
                                ok,
                                LazyFormat(
                                    "no exception when casting %s into %s" % (m, T)
                                ),
                            )
                        if sn:
                            tester.assertEqual(
                                n,
                                self(T(n)),
                                LazyFormat(
                                    "casting %s into %s destroys element" % (n, T)
                                ),
                            )
                        else:
                            tester.assertTrue(
                                T(n).is_zero(),
                                LazyFormat("%s does not map to zero in %s" % (n, T)),
                            )
                        if sm:
                            tester.assertEqual(
                                a * T(m),
                                T(am),
                                LazyFormat("bad action %s * %s != %s" % (a, m, n)),
                            )
            # FIXME: run the TestSuite of a truncation (and avoid infinite loops)

        def _test_suspension(self, tester=None, **options):
            from sage.misc.sage_unittest import TestSuite
            from sage.misc.lazy_format import LazyFormat

            is_sub_testsuite = tester is not None
            tester = self._tester(tester=tester, **options)
            myatt = "_suspension_tested"
            if not hasattr(self, myatt):
                s = self.an_element()
                X = suspension(self, t=5, s=3)
                tester.assertTrue(
                    X is suspension(self, t=5, s=3),
                    LazyFormat("suspension(X,..) is not suspension(X,..) for X=%s")
                    % (X,),
                )
                setattr(X, myatt, "yo")
                try:
                    tester.info("\n  Running the test suite of a suspension")
                    TestSuite(X).run(
                        verbose=tester._verbose,
                        prefix=tester._prefix + "  ",
                        raise_on_failure=is_sub_testsuite,
                    )
                    tester.info(tester._prefix + " ", newline=False)
                    x = s.suspend(t=5, s=3)
                    x3 = s.suspend(t=5, s=3)
                    x2 = self.suspend_element(s, t=5, s=3)
                    tester.assertEqual(
                        x,
                        x3,
                        LazyFormat(
                            "x.suspend(...) != x.suspend(...):\n   A=%s\n   B=%s"
                        )
                        % (
                            x,
                            x3,
                        ),
                    )
                    tester.assertEqual(
                        x,
                        x2,
                        LazyFormat(
                            "x.suspend(...) != parent.suspend_element(x,...):\n   A=%s\n   B=%s"
                        )
                        % (
                            x,
                            x2,
                        ),
                    )
                    tester.assertTrue(
                        x.parent() == X,
                        LazyFormat("suspended element %s not in suspension %s")
                        % (
                            x,
                            X,
                        ),
                    )
                finally:
                    delattr(X, myatt)

        def _test_cartesian_product(self, tester=None, **options):
            from sage.misc.sage_unittest import TestSuite
            from sage.misc.lazy_format import LazyFormat

            if hasattr(self, "_suspension_tested"):
                return  # avoids infinity test cycle
            is_sub_testsuite = tester is not None
            tester = self._tester(tester=tester, **options)
            myatt = "_ycp_cartesian_product_tested"
            if not hasattr(self, myatt):
                X = cartesian_product((self, self))
                setattr(X, myatt, "yo")
                try:
                    tester.info("\n  Running the test suite of (self (+) self)")
                    TestSuite(X).run(
                        verbose=tester._verbose,
                        prefix=tester._prefix + "  ",
                        raise_on_failure=is_sub_testsuite,
                    )
                    f = X.cartesian_projection(0)
                    tester.info(
                        "\n  Running the test suite of the projection (self (+) self) -> self"
                    )
                    TestSuite(f).run(
                        verbose=tester._verbose,
                        prefix=tester._prefix + "  ",
                        raise_on_failure=is_sub_testsuite,
                        skip=[
                            "_test_category",
                            "_test_nonzero_equal",
                            "_test_pickling",
                        ],
                    )
                    f = X.summand_embedding(1)
                    tester.info(
                        "\n  Running the test suite of the embedding self -> (self (+) self)"
                    )
                    TestSuite(f).run(
                        verbose=tester._verbose,
                        prefix=tester._prefix + "  ",
                        raise_on_failure=is_sub_testsuite,
                        skip=[
                            "_test_category",
                            "_test_nonzero_equal",
                            "_test_pickling",
                        ],
                    )
                finally:
                    delattr(X, myatt)

        def dump_element(self, el):
            """
            Create a string representation of the element.
            The default implementation uses 'dumps' and is very inefficient.

            .. note:: the string must be unambigously determined by the element.
            """
            import base64

            return base64.b64encode(dumps(el))

        def load_element(self, str):
            """
            Create element from its string representation.
            The default implementation uses 'loads' and is very inefficient.
            """
            import base64

            return loads(bse64.b64decode(str))

        def _test_dump_element(self, tester=None, **options):
            tester = self._tester(tester=tester, **options)
            from sage.misc.sage_unittest import TestSuite
            from sage.misc.lazy_format import LazyFormat

            for (cnt, el) in zip(list(range(0, 10)), self.some_elements()):
                str = self.dump_element(el)
                oth = self.load_element(str)
                tester.assertEqual(
                    el,
                    oth,
                    LazyFormat("load_element(dump_element(el)) != el for el = %s") % el,
                )

        def _can_test_pickling(self):
            """
            Some objects (e.g., morphisms, kernels of morphisms, ...) cannot be pickled.
            """
            return True

    class ElementMethods:
        def _can_test_pickling(self):
            return self.parent()._can_test_pickling()

        def differential(self):
            return self.parent().differential(self)

    class TensorProducts(TensorProductsCategory):
        """
        tensor products of Steenrod algebra modules.
        """

        def extra_super_categories(self):
            return [self.base_category()]

        def Subquotients(self):
            return self.base_category().Subquotients()

        def _repr_object_names(self):
            return "tensor products of %s" % self.base_category()._repr_object_names()

        class ParentMethods:
            def _can_test_pickling(self):
                return all(M._can_test_pickling() for M in self._sets)

            def _differential_on_basis(self, keys):
                """
                Internal differential of a tensor product of modules

                TESTS::

                    sage: fix me!
                """
                ans = []
                for (i, mod) in enumerate(self._sets):
                    a = keys[:i]
                    b = mod.differential(mod.monomial(keys[i]))
                    c = keys[i + 1 :]
                    for (key, cf) in b:
                        if 0 != (i & 1):
                            cf = -cf
                        ans.append(
                            (
                                tuple(
                                    list(a)
                                    + [
                                        key,
                                    ]
                                    + list(c)
                                ),
                                cf,
                            )
                        )
                return self._from_dict(dict(ans))

            @staticmethod
            def SuspendedObjectsFactory(module, *args, **kwopts):
                from sage.categories.tensor import tensor

                l = len(module._sets)
                last = module._sets[l - 1]
                newsets = list(module._sets[: l - 1]) + [
                    suspension(last, *args, **kwopts),
                ]
                return tensor(tuple(newsets))

        class ElementMethods:
            def _can_test_pickling(self):
                return self.parent()._can_test_pickling()

        class Subquotients(SubquotientsCategory):
            """
            A subobject or quotient of a tensor product is no longer a tensor product
            """
            def _repr_object_names(self):
                return "subquotients of %s" % self.base_category()._repr_object_names()

            def extra_super_categories(self):
                return []

            def super_categories(self):
                return [self.base_category().base_category().Subquotients()]

    class CartesianProducts(CartesianProductsCategory):
        """
        direct sums of modules.
        """

        def extra_super_categories(self):
            """
            TESTS::

            sage: from yacop.categories import *
            sage: import yacop
            sage: yacop.categories.utils.yacop_supercategories(YacopDifferentialModules(SteenrodAlgebra(3)).CartesianProducts())
            [Category of Cartesian products of yacop differential modules over mod 3 Steenrod algebra, milnor basis,
            Category of yacop differential modules over mod 3 Steenrod algebra, milnor basis,
            Category of Cartesian products of yacop graded objects,
            Category of yacop graded objects,
            Category of yacop objects]

            """
            return [self.base_category()]

        class Subquotients(SubquotientsCategory):
            """
            A subobject or quotient of a direct sum is no longer a direct sum
            """
            def _repr_object_names(self):
                return "subquotients of %s" % self.base_category()._repr_object_names()

            def extra_super_categories(self):
                return []

            def super_categories(self):
                return [self.base_category().base_category().Subquotients()]

        class ElementMethods:
            def _can_test_pickling(self):
                return self.parent()._can_test_pickling()

        class ParentMethods:
            def _differential_on_basis(self, key):
                idx, k = key
                mod = self._sets[idx]
                return self.summand_embedding(idx)(mod.differential(mod.monomial(k)))

            def _repr_term(self, elem):
                return "(%s)" % ", ".join(
                    mod._repr_term(mod.cartesian_projection(i)(elem))
                    for (mod, i) in zip(self._sets, self._set_keys)
                )

            def suspend_element(self, m, **options):
                susp = suspension(self, **options)
                smds = []
                for i in range(0, len(self._sets)):
                    Mi = self._sets[i]
                    mi = self.cartesian_projection(i)(m)
                    mis = Mi.suspend_element(mi, **options)
                    # hack: we might have nonidentical parents here: mis.parent() != susp._sets[i]
                    mis._set_parent(susp._sets[i])
                    smds.append(susp.summand_embedding(i)(mis))
                return susp.sum(smds)

            @staticmethod
            def SuspendedObjectsFactory(module, *args, **kwopts):
                from sage.categories.cartesian_product import cartesian_product

                return cartesian_product(
                    [suspension(mod, *args, **kwopts) for mod in module._sets]
                )

            def _can_test_pickling(self):
                return all(m._can_test_pickling() for m in self._sets)

    class DualObjects(DualObjectsCategory):
        def extra_super_categories(self):
            r"""
            Returns the dual category

            EXAMPLES:

            The category of algebras over the Rational Field is dual
            to the category of coalgebras over the same field::

                sage: C = Algebras(QQ)
                sage: C.dual()
                Category of duals of algebras over Rational Field
                sage: C.dual().extra_super_categories()
                [Category of coalgebras over Rational Field]
            """
            from sage.categories.coalgebras import Coalgebras

            return [Coalgebras(self.base_category().base_ring())]

        def Subquotients(self):
            """
            A subobject or quotient of a direct sum is no longer a direct sum
            """
            return self.base_category().Subquotients()

    class SuspendedObjects(SuspendedObjectsCategory):

        """
        TESTS::

            sage: import yacop.modules
            sage: C=yacop.categories.YacopLeftModuleAlgebras(SteenrodAlgebra(3))
            sage: C.SuspendedObjects()
            Category of suspensions of yacop left module algebras over mod 3 Steenrod algebra, milnor basis

        """

        @cached_method
        def extra_super_categories(self):
            return [self.base_category().ModuleCategory()]

        def base_ring(self):
            return self.base_category().base_ring()

        class ParentMethods:
            pass

    class TruncatedObjects(TruncatedObjectsCategory):

        """
        TESTS::

            sage: import yacop.modules
            sage: C=yacop.categories.YacopLeftModuleAlgebras(SteenrodAlgebra(3))
            sage: C.TruncatedObjects()
            Category of truncations of yacop left module algebras over mod 3 Steenrod algebra, milnor basis

        """

        @cached_method
        def extra_super_categories(self):
            return [self.base_category().ModuleCategory()]

        def base_ring(self):
            return self.base_category().base_ring()

        class ParentMethods:
            pass

    class Homsets(HomsetsCategory):
        """
        TESTS::

            sage: from yacop.categories import *
            sage: C = YacopLeftModules(SteenrodAlgebra(3))
            sage: C.Homsets()
            Category of homsets of yacop left modules over mod 3 Steenrod algebra, milnor basis
        """

        def _repr_object_names(self):
            return "homsets of %s" % self.base_category()._repr_object_names()

        def extra_super_categories(self):
            # TODO: make this a Steenrod algebra module
            return [
                ModulesWithBasis(
                    self.base_category().ModuleCategory().base_ring()
                ).Homsets(),
            ]

        def super_categories(self):
            # TODO: make this a Steenrod algebra module
            return [
                ModulesWithBasis(
                    self.base_category().ModuleCategory().base_ring()
                ).Homsets(),
            ]

        class ParentMethods:
            pass

        class ElementMethods:
            def _test_nonzero_equal(self, **options):
                pass

            def kernel(self):
                M = self.domain()
                if hasattr(M, "KernelOf"):
                    return M.KernelOf(self)
                raise NotImplementedError("kernel of map from %s not implemented" % M)

            def image(self):
                N = self.codomain()
                if hasattr(N, "ImageOf"):
                    return N.ImageOf(self)
                raise NotImplementedError("image of map into %s not implemented" % N)

            def cokernel(self):
                N = self.codomain()
                if hasattr(N, "CokernelOf"):
                    return N.CokernelOf(self)
                raise NotImplementedError("cokernel of map into %s not implemented" % N)

            @staticmethod
            def SuspendedObjectsFactory(self, *args, **kwopts):
                """
                suspension of morphisms.

                TESTS::

                   sage: from yacop.categories.functors import suspension
                   sage: from yacop.modules.all import BZp
                   sage: M = BZp(3)
                   sage: X = cartesian_product((M,M))
                   sage: f = X.cartesian_projection(0)
                   sage: sf = suspension(f,t=5)
                   sage: sf.domain() is suspension(f.domain(),t=5)
                   True
                   sage: sf.codomain() is suspension(f.codomain(),t=5)
                   True
                   sage: x = X.an_element()
                   sage: sf(x.suspend(t=5)) == f(x).suspend(t=5)
                   True

                """
                M, N = self.domain(), self.codomain()
                SM, SN = [suspension(x, **kwopts) for x in (M, N)]
                lam = lambda i: self(M.monomial(i)).suspend(**kwopts)
                res = SM.module_morphism(codomain=SN, on_basis=lam)
                res.rename("suspension of %s" % self)
                return res

            def _test_suspension(self, tester=None):
                pass

    class Subquotients(SubquotientsCategory):
        """
        A subquotient of a Steenrod algebra module or algebra

        TESTS::

            sage: from yacop.categories import *
            sage: C = YacopLeftModuleAlgebras(SteenrodAlgebra(11))
            sage: D = YacopLeftModules(SteenrodAlgebra(11))
            sage: C.Subquotients()
            Category of subquotients of yacop left module algebras over mod 11 Steenrod algebra, milnor basis
            sage: D.Subquotients()
            Category of subquotients of yacop left modules over mod 11 Steenrod algebra, milnor basis
        """

        def _repr_object_names(self):
            return "subquotients of %s" % self.base_category()._repr_object_names()

        @cached_method
        def super_categories(self):
            """
            A subquotient should again be a Steenrod algebra module, but not an algebra.

            TESTS::

                sage: from yacop.categories import *
                sage: C = YacopLeftModules(SteenrodAlgebra(3))
                sage: D = C.Subquotients() ; D
                Category of subquotients of yacop left modules over mod 3 Steenrod algebra, milnor basis
                sage: C in D.all_super_categories()
                True
                sage: E = YacopLeftModuleAlgebras(SteenrodAlgebra(3))
                sage: F = E.Subquotients() ; F
                Category of subquotients of yacop left module algebras over mod 3 Steenrod algebra, milnor basis
                sage: C in F.all_super_categories()
                True
                sage: E in F.all_super_categories()
                False

            """
            return [self.base_category().ModuleCategory()]

        class ParentMethods:
            def lift(self, elem):
                """
                Lift an element of ``self`` to ``self.ambient()`` as per ``Subquotients`` category.

                This default implementation delegates its work to self._lift_homogeneous.
                """
                ans = []
                for (deg, smd) in list(elem.homogeneous_decomposition().items()):
                    ans.append(self._lift_homogeneous(deg, smd))
                return self.parent().ambient().sum(ans)

            def retract(self, elem):
                """
                Retract an element of ``self.ambient()`` to ``self`` as per ``Subquotients`` category.

                This default implementation delegates its work to self._retract_homogeneous.
                """
                ans = []
                for (deg, smd) in list(elem.homogeneous_decomposition().items()):
                    ans.append(self._retract_homogeneous(deg, smd))
                return self.parent().sum(ans)


"""
  TESTS::

      sage: import __main__
      sage: from yacop.categories.differential_modules import YacopDifferentialModules
      sage: __main__.YacopDifferentialModules = YacopDifferentialModules
      sage: TestSuite(YacopDifferentialModules(SteenrodAlgebra(3))).run()
"""

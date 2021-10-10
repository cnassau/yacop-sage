r"""
Steenrod algebra modules

The Yacop base category for modules over the Steenrod algebra.

AUTHORS:

 - Christian Nassau (2011): initial revision

"""
# *****************************************************************************
#  Copyright (C) 2011      Christian Nassau <nassau@nullhomotopie.de>
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
from yacop.categories.utils import steenrod_antipode, category_meet
from sage.categories.category_with_axiom import CategoryWithAxiom_over_base_ring


def module_method(f):
    f.yacop_module_method = True
    return f


from types import MethodType, FunctionType
import re


class FiniteDimensional(CategoryWithAxiom_over_base_ring):
    """
    We want to overwrite the "kernel" (and other) methods from the MorphismMethods
    of the finite dimensional modules with basis category. This seems not possible
    as long as the finite dimensional modules category is a super category of
    YacopLeftModuleAlgebras.FiniteDimensional(). We therefore get rid of those
    functions entirely by creating our own category of finite dimensional modules.

    TESTS::

        sage: from yacop.categories import YacopLeftModuleAlgebras
        sage: C=YacopLeftModuleAlgebras(SteenrodAlgebra(2))
        sage: C._with_axiom_as_tuple('FiniteDimensional')
        (Category of finite dimensional yacop left module algebras over mod 2 Steenrod algebra, milnor basis,)

    """

    def super_categories(self):
        return [
            self.base_category(),
        ]

    def extra_super_categories(self):
        return []


# a decorator with arguments to refactor common code from
# the yacop module categories
class yacop_category:
    def __init__(
        self,
        left_action=False,
        right_action=False,
        is_algebra=False,
        module_category=None,
    ):
        self.left = left_action
        self.right = right_action
        self.algebra = is_algebra
        self.modules = module_category

    def is_yacop_method(self, name, meth):
        if name in ["__contains__", "__yacop_category__"]:
            return True
        if re.match("^__", name):
            return False
        if not isinstance(meth, FunctionType):
            # probably a cached or abstract method
            return True
        if hasattr(meth, "yacop_module_method") and getattr(
            meth, "yacop_module_method"
        ):
            return True
        return False

    def __call__(self, cls):
        cls._yacop_category = (self.left, self.right, self.algebra)
        for (name, meth) in CommonParentMethods.__dict__.items():
            if self.is_yacop_method(name, meth):
                setattr(cls.ParentMethods, name, meth)
        for (name, meth) in CommonCategoryMethods.__dict__.items():
            if self.is_yacop_method(name, meth) and not name in cls.__dict__:
                setattr(cls, name, meth)
        cls._yacop_modules_class = self.modules if not self.modules is None else cls

        if not self.algebra:
            cls.FiniteDimensional = FiniteDimensional

        __class__ = cls

        @cached_method
        def is_subcategory(self, other):
            """
            Subcategory detection was broken by Trac #16618. This is a hack to fix some of those problems.

            TESTS::

                sage: from yacop.categories import *
                sage: YacopLeftModules(SteenrodAlgebra(2)).is_subcategory(ModulesWithBasis(GF(2)))
                True

            """
            for scat in self.super_categories():
                if scat.is_subcategory(other):
                    return True
            return super().is_subcategory(other)

        if not "is_subcategory" in cls.__dict__:
            cls.is_subcategory = is_subcategory

        def yes(self):
            return True

        if self.left:
            cls.SubcategoryMethods._yacop_has_left_action = yes

        if self.right:
            cls.SubcategoryMethods._yacop_has_right_action = yes

        if self.algebra:
            cls.SubcategoryMethods._yacop_has_multiplication = yes

        return cls


class CommonCategoryMethods:
    @module_method
    def ModuleCategory(self):
        """
        Forget the algebra structure if present:

        TESTS::

           sage: from yacop.categories import *
           sage: SteenrodAlgebraModulesAlgebras(SteenrodAlgebra(3)).ModuleCategory() is SteenrodAlgebraModules(SteenrodAlgebra(3))
           True

        """
        return self._yacop_modules_class(self.base_ring())

    @cached_method
    @module_method
    def _meet_(self, other):
        """
        TESTS::

            sage: from yacop.categories import *
            sage: A2 = SteenrodAlgebra(2,profile=(3,2,1))
            sage: A = SteenrodAlgebra(2)
            sage: B = SteenrodAlgebra(3)
            sage: YacopLeftModules(A)._meet_(YacopLeftModules(A2))
            Category of yacop left modules over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
            sage: YacopLeftModules(A2)._meet_(YacopLeftModules(A))
            Category of yacop left modules over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
            sage: YacopLeftModules(A)._meet_(YacopLeftModules(A))
            Category of yacop left modules over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis

        """
        return category_meet(self, other)

    @cached_method
    @module_method
    def super_categories(self):
        """
        TESTS::

            sage: from yacop.categories import *
            sage: A=SteenrodAlgebra(3)
            sage: YacopLeftModules(A).super_categories()
            [Category of yacop differential modules over mod 3 Steenrod algebra, milnor basis,
             Category of vector spaces with basis over Finite Field of size 3,
             Category of left modules over mod 3 Steenrod algebra, milnor basis]
            sage: YacopRightModules(A).super_categories()
            [Category of yacop differential modules over mod 3 Steenrod algebra, milnor basis,
             Category of vector spaces with basis over Finite Field of size 3,
             Category of right modules over mod 3 Steenrod algebra, milnor basis]
            sage: YacopBimodules(A).super_categories()
            [Category of yacop differential modules over mod 3 Steenrod algebra, milnor basis,
             Category of vector spaces with basis over Finite Field of size 3,
             Category of bimodules over mod 3 Steenrod algebra, milnor basis on the left and mod 3 Steenrod algebra, milnor basis on the right]
            sage: YacopLeftModuleAlgebras(A).super_categories()
            [Category of yacop differential modules over mod 3 Steenrod algebra, milnor basis,
             Category of vector spaces with basis over Finite Field of size 3,
             Category of left modules over mod 3 Steenrod algebra, milnor basis,
             Category of algebras with basis over Finite Field of size 3]
            sage: YacopRightModuleAlgebras(A).super_categories()
            [Category of yacop differential modules over mod 3 Steenrod algebra, milnor basis,
             Category of vector spaces with basis over Finite Field of size 3,
             Category of right modules over mod 3 Steenrod algebra, milnor basis,
             Category of algebras with basis over Finite Field of size 3]
            sage: YacopBimoduleAlgebras(A).super_categories()
            [Category of yacop differential modules over mod 3 Steenrod algebra, milnor basis,
             Category of vector spaces with basis over Finite Field of size 3,
             Category of bimodules over mod 3 Steenrod algebra, milnor basis on the left and mod 3 Steenrod algebra, milnor basis on the right,
             Category of algebras with basis over Finite Field of size 3]

        """
        from sage.categories.modules_with_basis import ModulesWithBasis
        from yacop.categories.differential_modules import YacopDifferentialModules

        (left, right, algebra) = self._yacop_category

        R = self.base_ring()
        x = []
        x.append(YacopDifferentialModules(R))
        x.append(ModulesWithBasis(R.base_ring()))
        if left and right:
            x.append(Bimodules(R, R))
        else:
            if left:
                x.append(LeftModules(R))
            if right:
                x.append(RightModules(R))
        if algebra:
            x.append(AlgebrasWithBasis(R.base_ring()))
        return x


class CommonParentMethods:
    @cached_method
    @module_method
    def __yacop_category__(self):
        # the list of categories should contain at most one yacop module category
        for cat in self.categories():
            try:
                if getattr(cat, "_yacop_modules_class") is not None:
                    return cat
            except:
                pass
        raise ValueError("internal error: cannot detect yacop category")

    @module_method
    def _test_category_contains(self, tester=None, **options):
        """
        Test the implicit __contains__ method of this category::

            sage: from yacop.modules.projective_spaces import RealProjectiveSpace
            sage: M=RealProjectiveSpace()
            sage: M.category()
            Category of yacop left module algebras over mod 2 Steenrod algebra, milnor basis
            sage: M in M.category()
            True
            sage: M._test_category_contains()

        """
        from sage.misc.lazy_format import LazyFormat
        from sage.rings.finite_rings.finite_field_constructor import FiniteField

        tester = self._tester(**options)
        tester.assertTrue(
            self in self.category(),
            LazyFormat("%s not contained in its category %s" % (self, self.category())),
        )
        M = ModulesWithBasis(FiniteField(self.base_ring().characteristic()))
        tester.assertTrue(self in M, LazyFormat("%s not contained in %s" % (self, M)))

    @module_method
    def _test_homset_sanity(self, tester=None, **options):
        """
        Test whether the identity can be constructed and has its kernel, coker, etc.
        in the right category. This can fail if Sage puts the wrong "kernel" method
        into the mro of the Homset category.
        """
        from sage.misc.lazy_format import LazyFormat

        tester = self._tester(**options)
        id = self.module_morphism(codomain=self, function=lambda x: x)
        wanted = self.__yacop_category__().Subquotients()
        tester.assertTrue(
            id.kernel() in wanted,
            LazyFormat("identity of %s has a bad kernel" % (self,)),
        )
        tester.assertTrue(
            id.cokernel() in wanted,
            LazyFormat("identity of %s has a bad cokernel" % (self,)),
        )
        tester.assertTrue(
            id.image() in wanted,
            LazyFormat("identity of %s has a bad image" % (self,)),
        )

    @module_method
    def _test_simple_truncation(self, tester=None, **options):
        """
        Test whether the module can be truncated.
        """
        from sage.misc.lazy_format import LazyFormat
        from yacop.categories.functors import truncation

        tester = self._tester(**options)

        pt = self.bbox().nearest_point(t=0,s=0,e=0)
        T = truncation(self,**pt.as_dict())

        tester.assertTrue(
            T.bbox() == pt,
            LazyFormat("bbox %s of %s seems wrong, expected %s" % (T.bbox(),T,pt)),
        )

        if False:
            # FIXME: this mostly fails
            el = T.an_element()

            tester.assertTrue(
                el.degree() == pt,
                LazyFormat("element %s of %s has wrong degree %s" % (el,T,el.degree())),
            )

    @module_method
    def _test_steenrod_action(self, tester=None, **options):
        from sage.misc.sage_unittest import TestSuite
        from sage.misc.lazy_format import LazyFormat

        tester = self._tester(**options)
        Y = self.__yacop_category__()
        A = Y.base_ring()
        elist = []
        try:
            # under exotic circumstances, this code can fail: #24988
            elist = list(A.some_elements())
            for e in A.homogeneous_component(2 * (A.prime() ** 3 - 1)).basis():
                elist.append(A(e))
        except:
            pass

        is_left = LeftModules(A) in Y.all_super_categories()
        is_right = RightModules(A) in Y.all_super_categories()

        x = self.an_element()
        for e in elist:
            if is_left:
                y = e * x  # does left action work?
                tester.assertEqual(
                    y,
                    steenrod_antipode(e) % x,
                    LazyFormat(
                        "conjugate action check failed: e.antipode()%x != e*x for x=%s, e=%s"
                    )
                    % (x, e),
                )
            if is_right:
                y = x * e  # does right action work?
                tester.assertEqual(
                    y,
                    x % steenrod_antipode(e),
                    LazyFormat(
                        "conjugate action check failed: x%e.antipode() != x*e for x=%s, e=%s"
                    )
                    % (x, e),
                )
            if is_left and is_right:
                tester.assertEqual(
                    (e * x) * e,
                    e * (x * e),
                    LazyFormat("bimodule check failed: (ex)e != e(xe) for x=%s, e=%s")
                    % (x, e),
                )
        if False:
            tester.assertTrue(
                bbox.__class__ == region,
                LazyFormat("bounding box of %s is not a region") % (self,),
            )

    @module_method
    def _manual_test_action(self, reg, opdeg=None, mode="left", verbose=False):
        """
        a check of the associativity of the steenrod algebra action
        """
        if mode == "left":

            def LHS(op1, op2, a):
                return (op1 * op2) * a

            def RHS(op1, op2, a):
                return op1 * (op2 * a)

        elif mode == "right":

            def LHS(op1, op2, a):
                return a * (op1 * op2)

            def RHS(op1, op2, a):
                return (a * op1) * op2

        elif mode == "bimod":

            def LHS(op1, op2, a):
                return (op1 * a) * op2

            def RHS(op1, op2, a):
                return op1 * (a * op2)

        elif mode == "leftconj":

            def LHS(op1, op2, a):
                return (op1 * op2) % a

            def RHS(op1, op2, a):
                return op2 % (op1 % a)

        elif mode == "rightconj":

            def LHS(op1, op2, a):
                return a % (op1 * op2)

            def RHS(op1, op2, a):
                return (a % op2) % op1

        elif mode == "bimodconj":

            def LHS(op1, op2, a):
                return (op1 % a) % op2

            def RHS(op1, op2, a):
                return op1 % (a % op2)

        else:
            raise ValueError("unknown mode %s" % mode)

        A = self._yacop_base_ring

        def abasis(i):
            for x in A[i].basis():
                yield A(x)

        cnt = 0
        for b in self.graded_basis(reg):
            odeg = opdeg if not opdeg is None else reg.tmax - b.t
            for i in range(0, odeg + 1):
                for op1 in abasis(i):
                    for j in range(0, odeg + 1 - i):
                        if verbose:
                            print(mode, b, i, j, cnt)
                        for op2 in abasis(j):
                            val = LHS(op1, op2, b)
                            if val != RHS(op1, op2, b):
                                print("ERROR (%s):" % mode)
                                print("op1", op1)
                                print("op2", op2)
                                print("  b", b)
                                print("LHS = ", LHS(op1, op2, b))
                                print("RHS = ", RHS(op1, op2, b))
                                raise ValueError("mismatch")
                            if not val.is_zero():
                                cnt += 1
        print("%d non-zero multiplications checked" % cnt)

    @module_method
    def _check_adem_relations(self, region=None, act_left=True):
        pass

    @module_method
    def _check_action(self, region=None, act_left=True):
        pass


class notused:
    @cached_method
    def __yacop_category__(self):
        # the list of categories should contain at most one yacop module category
        for cat in self.categories():
            try:
                if cat._is_yacop_module_category:
                    return cat
            except:
                pass
        raise ValueError("internal error: cannot detect yacop category")


    # some routines (for example the combinatorial free modules' cartesian_product
    # cartesian_projection) use the underscored version instead
    #_module_morphism = module_morphism

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
            for (deg, m) in self.an_element().homogeneous_decomposition().items():
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
                            LazyFormat("contains (+) broken for %s (elem %s)") % (T, n),
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
                            LazyFormat("contains (-) broken for %s (elem %s)") % (T, n),
                        )
                        ok = False
                        try:
                            x = T(m)
                        except:
                            ok = True
                        tester.assertTrue(
                            ok,
                            LazyFormat("no exception when casting %s into %s" % (m, T)),
                        )
                    if sn:
                        tester.assertEqual(
                            n,
                            self(T(n)),
                            LazyFormat("casting %s into %s destroys element" % (n, T)),
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
                LazyFormat("suspension(X,..) is not suspension(X,..) for X=%s") % (X,),
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
                    LazyFormat("x.suspend(...) != x.suspend(...):\n   A=%s\n   B=%s")
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
                    skip=["_test_category", "_test_nonzero_equal", "_test_pickling"],
                )
                f = X.summand_embedding(1)
                tester.info(
                    "\n  Running the test suite of the embedding self -> (self (+) self)"
                )
                TestSuite(f).run(
                    verbose=tester._verbose,
                    prefix=tester._prefix + "  ",
                    raise_on_failure=is_sub_testsuite,
                    skip=["_test_category", "_test_nonzero_equal", "_test_pickling"],
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


class CommonElementMethods:
    pass

def allyc(R):
    from sage.categories.category_types import JoinCategory
    import re
    lst = []
    def descend(x):
        if not re.match(".*yacop",str(x)):
            return
        if x in lst or len(lst)>100:
            return
        if isinstance(x,JoinCategory):
            for y in x.super_categories():
                descend(y)
            return
        lst.append(x)
        #print(x)
        try:
            descend(x.CartesianProducts())
        except:
            pass
        try:
            descend(x.TensorProducts())
        except:
            pass
        try:
            descend(x.SuspendedObjects())
        except:
            pass
        try:
            descend(x.Subquotients())
        except:
            pass
    descend(R)
    return sorted(str(x) for x in lst)

r"""
Steenrod algebra modules

The Yacop base category for modules over the Steenrod algebra.


AUTHORS:

 - Christian Nassau (2011): initial revision

"""
#*****************************************************************************
#  Copyright (C) 2011      Christian Nassau <nassau@nullhomotopie.de>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************
#pylint: disable=E0213

from sage.rings.infinity import Infinity
from sage.misc.abstract_method import abstract_method
from sage.misc.cachefunc import cached_method
from sage.misc.lazy_attribute import lazy_attribute
from sage.categories.category_singleton import Category_singleton
from sage.categories.category_types import Category_over_base_ring
from sage.categories.homsets import HomsetsCategory
from sage.categories.all import Category, Sets, Hom, Rings, Modules, LeftModules, RightModules, Bimodules, ModulesWithBasis, AlgebrasWithBasis
from sage.categories.objects import Objects
from sage.categories.cartesian_product import CartesianProductsCategory, cartesian_product
from sage.categories.subquotients import SubquotientsCategory
from sage.categories.algebra_functor import AlgebrasCategory
from sage.categories.dual import DualObjectsCategory
from sage.categories.tensor import TensorProductsCategory, tensor
from sage.categories.morphism import SetMorphism
from sage.misc.cachefunc import cached_method
from sage.structure.sage_object import SageObject
from sage.structure.element import have_same_parent
from yacop.utils.region import region
from yacop.modules.functors import SuspendedObjectsCategory
from yacop.modules.functors import TruncatedObjectsCategory
from sage.misc.cachefunc import cached_function
from sage.misc.classcall_metaclass import typecall, ClasscallMetaclass
from yacop.modules.functors import suspension
from sage.misc.lazy_attribute import lazy_attribute
from sage.rings.all import GF
from sage.categories.homset import Homset
from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra


class CommonParentMethods:

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
            for e in A.homogeneous_component(2*(A.prime()**3-1)).basis():
                elist.append(A(e))
        except:
            pass

        x = self.an_element()
        for e in elist:
            if Y._is_left:
                y = e*x        # does left action work?
                tester.assertEqual(y, steenrod_antipode(e) % x,
                                    LazyFormat(
                                        "conjugate action check failed: e.antipode()%x != e*x for x=%s, e=%s")
                                    % (x, e))
            if Y._is_right:
                y = x*e        # does right action work?
                tester.assertEqual(y, x % steenrod_antipode(e),
                                    LazyFormat(
                                        "conjugate action check failed: x%e.antipode() != x*e for x=%s, e=%s")
                                    % (x, e))
            if Y._is_bimod:
                tester.assertEqual((e*x)*e, e*(x*e),
                                    LazyFormat(
                                        "bimodule check failed: (ex)e != e(xe) for x=%s, e=%s")
                                    % (x, e))
        if False:
            tester.assertTrue(bbox.__class__ == region,
                                LazyFormat("bounding box of %s is not a region") % (self,))

    def _manual_test_action(self, reg, opdeg=None, mode='left', verbose=False):
        """
        a check of the associativity of the steenrod algebra action
        """
        if mode == 'left':
            def LHS(op1, op2, a): return (op1*op2)*a
            def RHS(op1, op2, a): return op1*(op2*a)
        elif mode == 'right':
            def LHS(op1, op2, a): return a*(op1*op2)
            def RHS(op1, op2, a): return (a*op1)*op2
        elif mode == 'bimod':
            def LHS(op1, op2, a): return (op1*a)*op2
            def RHS(op1, op2, a): return op1*(a*op2)
        elif mode == 'leftconj':
            def LHS(op1, op2, a): return (op1*op2) % a
            def RHS(op1, op2, a): return op2 % (op1 % a)
        elif mode == 'rightconj':
            def LHS(op1, op2, a): return a % (op1*op2)
            def RHS(op1, op2, a): return (a % op2) % op1
        elif mode == 'bimodconj':
            def LHS(op1, op2, a): return (op1 % a) % op2
            def RHS(op1, op2, a): return op1 % (a % op2)
        else:
            raise ValueError("unknown mode %s" % mode)

        A = self._yacop_base_ring

        def abasis(i):
            for x in A[i].basis():
                yield A(x)
        cnt = 0
        for b in self.graded_basis(reg):
            odeg = opdeg if not opdeg is None else reg.tmax - b.t
            for i in range(0, odeg+1):
                for op1 in abasis(i):
                    for j in range(0, odeg+1-i):
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

    def _Hom_(X, Y, category):
        # here we overwrite the Rings._Hom_ implementation
        return Homset(X, Y, category=category)

    def module_morphism(self, *args, **kwargs):
        """
        TESTS::

            sage: from yacop.modules.categories import *
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
        cat = kwargs.pop('category', Y)
        codomain = kwargs.pop('codomain', self)
        cat = cat.category().meet((self.category(), codomain.category()))
        kwargs['category'] = cat
        kwargs['codomain'] = codomain
        ans = ModulesWithBasis(Y.base_ring().base_ring(
        )).parent_class.module_morphism(self, *args, **kwargs)
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

    def _xx_test_truncation(self, tester=None, **options):
        from yacop.modules.functors import truncation
        from sage.misc.sage_unittest import TestSuite
        from sage.misc.lazy_format import LazyFormat
        is_sub_testsuite = (tester is not None)
        tester = self._tester(tester=tester, **options)
        myatt = "_truncation_tested"
        if not hasattr(self, myatt):
            # find a non-zero action a*m = n in self
            def testops(A):
                for _ in A.some_elements():
                    yield _
                maxdeg = A.prime()**3
                for deg in range(1, maxdeg):
                    for key in A.homogeneous_component(maxdeg-deg+1).basis():
                        yield A(key)
            n = self.zero()
            for (deg, m) in self.an_element().homogeneous_decomposition().items():
                if not m.is_zero():
                    for a in testops(self._yacop_base_ring):
                        n = a*m
                        #print("trying %s*%s->%s"%(a,m,n))
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
                        tester.assertTrue(m in T,
                                            LazyFormat("contains (+) broken for %s (elem %s)") % (T, n))
                        tester.assertTrue(self(T(m)) == m,
                                            LazyFormat("casting from/to truncation broken for %s (elem %s)") % (T, n))
                        tester.assertTrue(T(m).parent() is T,
                                            LazyFormat("wrong parent for %s (elem %s)") % (T, n))
                    else:
                        tester.assertTrue(not m in T,
                                            LazyFormat("contains (-) broken for %s (elem %s)") % (T, n))
                        ok = False
                        try:
                            x = T(m)
                        except:
                            ok = True
                        tester.assertTrue(ok,
                                            LazyFormat("no exception when casting %s into %s" % (m, T)))
                    if sn:
                        tester.assertEqual(n, self(T(n)),
                                            LazyFormat("casting %s into %s destroys element" % (n, T)))
                    else:
                        tester.assertTrue(T(n).is_zero(),
                                            LazyFormat("%s does not map to zero in %s" % (n, T)))
                    if sm:
                        tester.assertEqual(a*T(m), T(am),
                                            LazyFormat("bad action %s * %s != %s" % (a, m, n)))
        # FIXME: run the TestSuite of a truncation (and avoid infinite loops)

    def _test_suspension(self, tester=None, **options):
        from sage.misc.sage_unittest import TestSuite
        from sage.misc.lazy_format import LazyFormat
        is_sub_testsuite = (tester is not None)
        tester = self._tester(tester=tester, **options)
        myatt = "_suspension_tested"
        if not hasattr(self, myatt):
            s = self.an_element()
            X = suspension(self, t=5, s=3)
            tester.assertTrue(X is suspension(self, t=5, s=3),
                                LazyFormat("suspension(X,..) is not suspension(X,..) for X=%s") % (X,))
            setattr(X, myatt, "yo")
            try:
                tester.info("\n  Running the test suite of a suspension")
                TestSuite(X).run(verbose=tester._verbose, prefix=tester._prefix+"  ",
                                    raise_on_failure=is_sub_testsuite)
                tester.info(tester._prefix+" ", newline=False)
                x = s.suspend(t=5, s=3)
                x3 = s.suspend(t=5, s=3)
                x2 = self.suspend_element(s, t=5, s=3)
                tester.assertEqual(x, x3,
                                    LazyFormat("x.suspend(...) != x.suspend(...):\n   A=%s\n   B=%s") % (x, x3,))
                tester.assertEqual(x, x2,
                                    LazyFormat("x.suspend(...) != parent.suspend_element(x,...):\n   A=%s\n   B=%s") % (x, x2,))
                tester.assertTrue(x.parent() == X,
                                    LazyFormat("suspended element %s not in suspension %s") % (x, X,))
            finally:
                delattr(X, myatt)

    def _test_cartesian_product(self, tester=None, **options):
        from sage.misc.sage_unittest import TestSuite
        from sage.misc.lazy_format import LazyFormat
        if hasattr(self, "_suspension_tested"):
            return  # avoids infinity test cycle
        is_sub_testsuite = (tester is not None)
        tester = self._tester(tester=tester, **options)
        myatt = "_ycp_cartesian_product_tested"
        if not hasattr(self, myatt):
            X = cartesian_product((self, self))
            setattr(X, myatt, "yo")
            try:
                tester.info(
                    "\n  Running the test suite of (self (+) self)")
                TestSuite(X).run(verbose=tester._verbose, prefix=tester._prefix+"  ",
                                    raise_on_failure=is_sub_testsuite)
                f = X.cartesian_projection(0)
                tester.info(
                    "\n  Running the test suite of the projection (self (+) self) -> self")
                TestSuite(f).run(verbose=tester._verbose, prefix=tester._prefix+"  ",
                                    raise_on_failure=is_sub_testsuite, skip=["_test_category", "_test_nonzero_equal", "_test_pickling"])
                f = X.summand_embedding(1)
                tester.info(
                    "\n  Running the test suite of the embedding self -> (self (+) self)")
                TestSuite(f).run(verbose=tester._verbose, prefix=tester._prefix+"  ",
                                    raise_on_failure=is_sub_testsuite, skip=["_test_category", "_test_nonzero_equal", "_test_pickling"])
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
            tester.assertEqual(el, oth,
                                LazyFormat("load_element(dump_element(el)) != el for el = %s") % el)

    def _can_test_pickling(self):
        """
        Some objects (e.g., morphisms, kernels of morphisms, ...) cannot be pickled.
        """
        return True

    def _check_adem_relations(self, region=None, act_left=True):
        pass

    def _check_action(self, region=None, act_left=True):
        pass


class CommonElementMethods:



# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

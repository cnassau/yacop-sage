r"""
Steenrod algebra modules

The Yacop base category for modules over the Steenrod algebra.

"""
# *****************************************************************************
#  Copyright (C) 2011-      Christian Nassau <nassau@nullhomotopie.de>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
# ******************************************************************************
# pylint: disable=E0213

from sage.misc.lazy_import import LazyImport, lazy_import
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
    RightModules,
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
from sage.categories.category_with_axiom import (
    CategoryWithAxiom_over_base_ring,
    base_category_class_and_axiom,
)

from yacop.categories.common import (
    CommonParentMethods,
    CommonElementMethods,
    CommonCategoryMethods,
)
from yacop.categories.common import yacop_category

from yacop.categories.differential_modules import YacopDifferentialModules
from yacop.categories.graded_objects import YacopGradedObjects
from yacop.categories.utils import SteenrodAlgebraAction, steenrod_antipode
from yacop.categories.utils import category_meet, steenrod_algebra_intersect
import operator


@yacop_category(right_action=True)
class YacopRightModules(Category_over_base_ring):
    """
    The category of Yacop right modules over the Steenrod algebra.

    EXAMPLES::

        sage: from yacop.categories import *
        sage: YacopRightModules(SteenrodAlgebra(7))
        Category of yacop right modules over mod 7 Steenrod algebra, milnor basis
    """

    def __init__(self, R):
        Category_over_base_ring.__init__(self, R)

    def an_instance(self):
        """
        EXAMPLE::

            sage: from yacop.categories import *
            sage: YacopRightModules(SteenrodAlgebra(2)).an_instance()
            mod 2 cohomology of real projective space P^{+Infinity}
            sage: YacopRightModules(SteenrodAlgebra(5)).an_instance()
            mod 5 cohomology of the classifying space of ZZ/5ZZ
        """
        from yacop.modules.all import RealProjectiveSpace, BZp

        if self.base_ring().is_generic():
            return BZp(self.base_ring().characteristic())
        else:
            return RealProjectiveSpace()

    def _repr_object_names(self):
        """
        TESTS::

            sage: from yacop.categories import YacopRightModules
            sage: A2 = SteenrodAlgebra(2,profile=(3,2,1))
            sage: A2.rename("A2")
            sage: YacopRightModules(A2)
            Category of yacop right modules over A2
        """
        return "yacop right modules over %s" % (self.base_ring())

    def is_subcategory(self, c):
        """
        Note: this method has known imperfections. Its purpose is only to make sure that
        an A module is automatically considered a B module when B is a subalgebra of
        the Steenrod algebra A.

        TESTS::

            sage: from yacop.categories import YacopRightModules, YacopRightModuleAlgebras
            sage: A=YacopRightModuleAlgebras(SteenrodAlgebra(2))
            sage: B=YacopRightModules(SteenrodAlgebra(2,profile=(2,1)))
            sage: C=YacopRightModuleAlgebras(SteenrodAlgebra(2,profile=(2,1)))
            sage: A.is_subcategory(B)
            True
            sage: C.is_subcategory(B)
            True

        """
        if isinstance(c,YacopRightModules) and steenrod_algebra_intersect((c.base_ring(),self.base_ring())) is c.base_ring():
            return True
        return super().is_subcategory(c)

    class ParentMethods:

        def __init_extra__(self):
            from yacop.categories.utils import SteenrodAlgebraAction
            import operator

            # register actions
            Y = self.__yacop_category__()
            self._yacop_base_ring = Y.base_ring()
            if not True:
                self.register_action(
                    SteenrodAlgebraAction(
                        Y.base_ring(),
                        self,
                        self.right_steenrod_action_on_basis,
                        is_left=True,
                    )
                )
                self.register_action(
                    SteenrodAlgebraAction(
                        Y.base_ring(),
                        self,
                        self.right_conj_steenrod_action_on_basis,
                        is_left=True,
                        op=operator.mod,
                    )
                )
            if True:
                self.register_action(
                    SteenrodAlgebraAction(
                        Y.base_ring(),
                        self,
                        self.right_steenrod_action_on_basis,
                        is_left=False,
                    )
                )
                self.register_action(
                    SteenrodAlgebraAction(
                        Y.base_ring(),
                        self,
                        self.right_conj_steenrod_action_on_basis,
                        is_left=False,
                        op=operator.mod,
                    )
                )

        @abstract_method(optional=True)
        def right_steenrod_action_milnor(self, ak, mk):
            """
            Compute the right action a*m where ak, mk are the basis keys of monomials
            in the Milnor basis version of the Steenrod algebra, resp. the module.

            TESTS::

                sage: from yacop.categories import YacopRightModules
                sage: class testclass(CombinatorialFreeModule):
                ....:     def __init__(self):
                ....:          CombinatorialFreeModule.__init__(self,GF(2),ZZ,category=YacopRightModules(SteenrodAlgebra(2)))
                ....:     def right_steenrod_action_milnor(self,ak,mk):
                ....:          return self.monomial((ak,mk))
                ....:     def _repr_term(self,k):
                ....:          a,b = k
                ....:          return "%s*[%d]" % (SteenrodAlgebra(2).monomial(a),b)
                sage: C = testclass()
                sage: Sq(3) * C.monomial(17)
                Sq(3)*[17]
                sage: Sq(3) % C.monomial(17)
                Sq(0,1)*[17] + Sq(3)*[17]

            """

        @abstract_method(optional=True)
        def right_steenrod_action_milnor(self, mk, ak):
            """
            Compute the right action m*a where ak, mk are the basis keys of monomials
            in the Milnor basis version of the Steenrod algebra, resp. the module.

            TESTS::

                sage: from yacop.categories import YacopRightModules
                sage: class testclass(CombinatorialFreeModule):
                ....:     def __init__(self):
                ....:          CombinatorialFreeModule.__init__(self,GF(2),ZZ,category=YacopRightModules(SteenrodAlgebra(2)))
                ....:     def right_steenrod_action_milnor(self,mk,ak):
                ....:          return self.monomial((ak,mk))
                ....:     def _repr_term(self,k):
                ....:          a,b = k
                ....:          return "[%d]*%s" % (b,SteenrodAlgebra(2).monomial(a))
                sage: C = testclass()
                sage: C.monomial(17) * Sq(3)
                [17]*Sq(3)
                sage: C.monomial(17) % Sq(3)
                [17]*Sq(0,1) + [17]*Sq(3)

            """

        @abstract_method(optional=True)
        def right_steenrod_action_milnor_conj(self, ak, mk):
            """
            Compute the conjugate action conj(a)*m where ak, mk are the basis keys of
            monomials in the Milnor basis version of the Steenrod algebra, resp. the module.

            TESTS::

                sage: from yacop.categories import YacopRightModules
                sage: class testclass(CombinatorialFreeModule):
                ....:     def __init__(self):
                ....:          CombinatorialFreeModule.__init__(self,GF(2),ZZ,category=YacopRightModules(SteenrodAlgebra(2)))
                ....:     def right_steenrod_action_milnor_conj(self,ak,mk):
                ....:          return self.monomial((ak,mk))
                ....:     def _repr_term(self,k):
                ....:          a,b = k
                ....:          return "%s%%[%d]" % (SteenrodAlgebra(2).monomial(a),b)
                sage: C = testclass()
                sage: Sq(3) * C.monomial(17)
                Sq(0,1)%[17] + Sq(3)%[17]
                sage: Sq(3) % C.monomial(17)
                Sq(3)%[17]
            """

        @abstract_method(optional=True)
        def right_steenrod_action_milnor_conj(self, mk, ak):
            """
            Compute the conjugate action m*conj(a) where ak, mk are the basis keys of
            monomials in the Milnor basis version of the Steenrod algebra, resp. the module.

            TESTS::

                sage: from yacop.categories import YacopRightModules
                sage: class testclass(CombinatorialFreeModule):
                ....:     def __init__(self):
                ....:          CombinatorialFreeModule.__init__(self,GF(2),ZZ,category=YacopRightModules(SteenrodAlgebra(2)))
                ....:     def right_steenrod_action_milnor_conj(self,ak,mk):
                ....:          return self.monomial((mk,ak))
                ....:     def _repr_term(self,k):
                ....:          a,b = k
                ....:          return "[%d]%%%s" % (b,SteenrodAlgebra(2).monomial(a))
                sage: C = testclass()
                sage: C.monomial(17) * Sq(3)
                [17]%Sq(0,1) + [17]%Sq(3)
                sage: C.monomial(17) % Sq(3)
                [17]%Sq(3)
            """

        @lazy_attribute
        def right_steenrod_action_on_basis(self):
            """
            TESTS::

                sage: from yacop.categories import YacopRightModules
                sage: class testclass(CombinatorialFreeModule):
                ....:     def __init__(self):
                ....:          CombinatorialFreeModule.__init__(self,GF(2),ZZ,category=YacopRightModules(SteenrodAlgebra(2)))
                ....:     def right_steenrod_action_milnor(self,ak,mk):
                ....:          print("right_steenrod_action_milnor(%s,%s)"%(ak,mk))
                ....:          return self.zero()
                ....:     def right_steenrod_action_milnor_conj(self,ak,mk):
                ....:          print("right_steenrod_action_milnor_conj(%s,%s)"%(ak,mk))
                ....:          return self.zero()
                sage: C = testclass()
                sage: Sq(3) * C.monomial(17)
                right_steenrod_action_milnor((3,),17)
                0
                sage: Sq(3) % C.monomial(17)
                right_steenrod_action_milnor_conj((3,),17)
                0
            """
            if self.right_steenrod_action_milnor is not NotImplemented:
                return self._right_action_from_milnor
            if self.right_steenrod_action_milnor_conj is not NotImplemented:
                return self._right_action_from_milnor_conj
            return NotImplemented

        @lazy_attribute
        def right_conj_steenrod_action_on_basis(self):
            if self.right_steenrod_action_milnor_conj is not NotImplemented:
                return self._right_conj_action_from_milnor_conj
            if self.right_steenrod_action_milnor is not NotImplemented:
                return self._right_conj_action_from_milnor
            return NotImplemented

        @lazy_attribute
        def right_steenrod_action_on_basis(self):
            """
            TESTS::

                sage: from yacop.categories import YacopRightModules
                sage: class testclass(CombinatorialFreeModule):
                ....:     def __init__(self):
                ....:          CombinatorialFreeModule.__init__(self,GF(2),ZZ,category=YacopRightModules(SteenrodAlgebra(2)))
                ....:     def right_steenrod_action_milnor(self,ak,mk):
                ....:          print("right_steenrod_action_milnor(%s,%s)"%(ak,mk))
                ....:          return self.zero()
                ....:     def right_steenrod_action_milnor_conj(self,ak,mk):
                ....:          print("right_steenrod_action_milnor_conj(%s,%s)"%(ak,mk))
                ....:          return self.zero()
                sage: C = testclass()
                sage: C.monomial(17) * Sq(3)
                right_steenrod_action_milnor(17,(3,))
                0
                sage: C.monomial(17) % Sq(3)
                right_steenrod_action_milnor_conj(17,(3,))
                0
            """
            if self.right_steenrod_action_milnor is not NotImplemented:
                return self._right_action_from_milnor
            if self.right_steenrod_action_milnor_conj is not NotImplemented:
                return self._right_action_from_milnor_conj
            return NotImplemented

        @lazy_attribute
        def right_conj_steenrod_action_on_basis(self):
            if self.right_steenrod_action_milnor_conj is not NotImplemented:
                return self._right_conj_action_from_milnor_conj
            if self.right_steenrod_action_milnor is not NotImplemented:
                return self._right_conj_action_from_milnor
            return NotImplemented

        # wrapper functions: use conjugate if direct implementation not provided

        def _right_action_from_milnor_conj(self, a, m):
            return self._action_from_milnor(
                self.right_steenrod_action_milnor_conj, a.antipode(), m
            )

        def _right_action_from_milnor_conj(self, m, a):
            return self._action_from_milnor(
                self.right_steenrod_action_milnor_conj, m, a.antipode()
            )

        def _right_conj_action_from_milnor(self, a, m):
            return self._action_from_milnor(
                self.right_steenrod_action_milnor, a.antipode(), m
            )

        def _right_conj_action_from_milnor(self, m, a):
            return self._action_from_milnor(
                self.right_steenrod_action_milnor, m, a.antipode()
            )

        # direct implementations of actions and conjugate actions

        def _right_action_from_milnor(self, a, m):
            return self._action_from_milnor(
                self.right_steenrod_action_milnor, a.milnor(), m
            )

        def _right_action_from_milnor(self, m, a):
            return self._action_from_milnor(
                self.right_steenrod_action_milnor, m, a.milnor()
            )

        def _right_conj_action_from_milnor_conj(self, a, m):
            return self._action_from_milnor(
                self.right_steenrod_action_milnor_conj, a.milnor(), m
            )

        def _right_conj_action_from_milnor_conj(self, m, a):
            return self._action_from_milnor(
                self.right_steenrod_action_milnor_conj, m, a.milnor()
            )

        def _action_from_milnor(self, actfunc, a, m):
            adct = a.monomial_coefficients()
            mdct = m.monomial_coefficients()
            res = []
            for ak, cf1 in adct.items():
                for mk, cf2 in mdct.items():
                    d = actfunc(ak, mk)
                    res.append((d, cf1 * cf2))
            return self.linear_combination(res)

        def _manual_test_right_action(self, reg, opdeg=None, verbose=False):
            return self._manual_test_action(
                reg, opdeg=opdeg, mode="right", verbose=verbose
            )

        def _manual_test_right_action(self, reg, opdeg=None, verbose=False):
            return self._manual_test_action(
                reg, opdeg=opdeg, mode="right", verbose=verbose
            )

        def _manual_test_bimod_action(self, reg, opdeg=None, verbose=False):
            return self._manual_test_action(
                reg, opdeg=opdeg, mode="bimod", verbose=verbose
            )

        def _manual_test_right_conj_action(self, reg, opdeg=None, verbose=False):
            return self._manual_test_action(
                reg, opdeg=opdeg, mode="rightconj", verbose=verbose
            )

        def _manual_test_right_conj_action(self, reg, opdeg=None, verbose=False):
            return self._manual_test_action(
                reg, opdeg=opdeg, mode="rightconj", verbose=verbose
            )

        def _manual_test_bimod_conj_action(self, reg, opdeg=None, verbose=False):
            return self._manual_test_action(
                reg, opdeg=opdeg, mode="bimodconj", verbose=verbose
            )

    class ElementMethods:
        pass

    class TensorProducts(TensorProductsCategory):
        """
        tensor products of Steenrod algebra modules.
        """

        def extra_super_categories(self):
            return [self.base_category()]

        yacop_no_default_inheritance = 1

        def Subquotients(self):
            """
            A subobject or quotient of a tensor product is no longer a tensor product.
            This is not easy to enforce because the Sage RegressiveCovariantConstructionCategory
            concept insists that X.Subquotients() always has X as super category.
            (See `meth: RegressiveCovariantConstructionCategory.default_super_categories`)
            We achieve this through a dirty hack in our startup script.

            TESTS::

                sage: from yacop.categories.right_modules import YacopRightModules
                sage: D=YacopRightModules(SteenrodAlgebra(3)).TensorProducts()
                sage: D in D.Subquotients().all_super_categories()
                False
                sage: from sage.categories.groups import Groups
                sage: from sage.categories.category_types import JoinCategory
                sage: J=JoinCategory((D,Groups()))
                sage: D in J.Subquotients().all_super_categories()
                False

            """
            return self.base_category().Subquotients()

        def _repr_object_names(self):
            return "tensor products of %s" % self.base_category()._repr_object_names()

        class ParentMethods:
            def _can_test_pickling(self):
                return all(M._can_test_pickling() for M in self._sets)

            def right_steenrod_action_on_basis(self, a, elem):
                return self.linear_combination(
                    (self.monomial(tuple(k)), c)
                    for (k, c) in self.__act_right(a, self._sets, elem)
                )

            def right_steenrod_action_on_basis(self, elem, a):
                return self.linear_combination(
                    (self.monomial(tuple(k)), c)
                    for (k, c) in self.__act_right(elem, self._sets, a)
                )

            def right_conj_steenrod_action_on_basis(self, a, elem):
                return self.linear_combination(
                    (self.monomial(tuple(k)), c)
                    for (k, c) in self.__act_right_conj(a, self._sets, elem)
                )

            def right_conj_steenrod_action_on_basis(self, elem, a):
                return self.linear_combination(
                    (self.monomial(tuple(k)), c)
                    for (k, c) in self.__act_right_conj(elem, self._sets, a)
                )

            def __act_right(self, a, parents, elem):
                for (key, cf) in elem:
                    M0 = parents[0]
                    m0 = M0._from_dict({key[0]: cf})
                    if len(parents) == 1:
                        for (k, c) in M0.right_steenrod_action_on_basis(a, m0):
                            yield [
                                k,
                            ], c
                    else:
                        A = a.parent()
                        cop = a.coproduct()
                        for ((k1, k2), acf) in cop:
                            a1 = A._from_dict({k1: acf})
                            a2 = A.monomial(k2)
                            deg2 = a2.degree()
                            for (k1, c1) in M0.right_steenrod_action_on_basis(a1, m0):
                                for (k, c) in self.__act_right(
                                    a2,
                                    parents[1:],
                                    [
                                        (key[1:], c1),
                                    ],
                                ):
                                    if (deg2 & 1) and (m0.e & 1):
                                        c = -c
                                    yield [
                                        k1,
                                    ] + k, c

            def __act_right(self, elem, parents, a):
                ln = len(parents) - 1
                for (key, cf) in elem:
                    M0 = parents[ln]
                    m0 = M0._from_dict({key[ln]: cf})
                    if len(parents) == 1:
                        for (k, c) in M0.right_steenrod_action_on_basis(m0, a):
                            yield [
                                k,
                            ], c
                    else:
                        A = a.parent()
                        cop = a.coproduct()
                        for ((k1, k2), acf) in cop:
                            a1 = A._from_dict({k1: acf})
                            a2 = A.monomial(k2)
                            deg1 = a1.degree()
                            for (k1, c1) in M0.right_steenrod_action_on_basis(m0, a2):
                                for (k, c) in self.__act_right(
                                    [
                                        (key[:ln], c1),
                                    ],
                                    parents[:ln],
                                    a1,
                                ):
                                    if (deg1 & 1) and (m0.e & 1):
                                        c = -c
                                    yield k + [
                                        k1,
                                    ], c

            def __act_right_conj(self, a, parents, elem):
                for (key, cf) in elem:
                    M0 = parents[0]
                    m0 = M0._from_dict({key[0]: cf})
                    if len(parents) == 1:
                        for (k, c) in M0.right_conj_steenrod_action_on_basis(a, m0):
                            yield [
                                k,
                            ], c
                    else:
                        A = a.parent()
                        cop = a.coproduct()
                        for ((k1, k2), acf) in cop:
                            a1 = A._from_dict({k1: acf})
                            a2 = A.monomial(k2)
                            deg2 = a2.degree()
                            for (k1, c1) in M0.right_conj_steenrod_action_on_basis(
                                a1, m0
                            ):
                                for (k, c) in self.__act_right_conj(
                                    a2,
                                    parents[1:],
                                    [
                                        (key[1:], c1),
                                    ],
                                ):
                                    if (deg2 & 1) and (m0.e & 1):
                                        c = -c
                                    yield [
                                        k1,
                                    ] + k, c

            def __act_right_conj(self, elem, parents, a):
                ln = len(parents) - 1
                for (key, cf) in elem:
                    M0 = parents[ln]
                    m0 = M0._from_dict({key[ln]: cf})
                    if len(parents) == 1:
                        for (k, c) in M0.right_conj_steenrod_action_on_basis(m0, a):
                            yield [
                                k,
                            ], c
                    else:
                        A = a.parent()
                        cop = a.coproduct()
                        for ((k1, k2), acf) in cop:
                            a1 = A._from_dict({k1: acf})
                            a2 = A.monomial(k2)
                            deg1 = a1.degree()
                            for (k1, c1) in M0.right_conj_steenrod_action_on_basis(
                                m0, a2
                            ):
                                for (k, c) in self.__act_right_conj(
                                    [
                                        (key[:ln], c1),
                                    ],
                                    parents[:ln],
                                    a1,
                                ):
                                    if (deg1 & 1) and (m0.e & 1):
                                        c = -c
                                    yield k + [
                                        k1,
                                    ], c

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

        class TruncatedObjects(TruncatedObjectsCategory):

            """
            TESTS::

                sage: import yacop.categories
                sage: C=yacop.categories.YacopRightModuleAlgebras(SteenrodAlgebra(3))
                sage: C.TensorProducts().TruncatedObjects()
                Category of truncations of yacop right module algebras over mod 3 Steenrod algebra, milnor basis

            """

            @cached_method
            def extra_super_categories(self):
                return [self.base_category()]

            def base_ring(self):
                return self.base_category().base_ring()

            class ParentMethods:
                pass

        class SuspendedObjects(SuspendedObjectsCategory):

            """
            TESTS::

                sage: import yacop.categories
                sage: C=yacop.categories.YacopRightModuleAlgebras(SteenrodAlgebra(3))
                sage: C.TensorProducts().SuspendedObjects()
                Category of truncations of yacop right module algebras over mod 3 Steenrod algebra, milnor basis

            """

            @cached_method
            def extra_super_categories(self):
                return [self.base_category()]

            def base_ring(self):
                return self.base_category().base_ring()

            class ParentMethods:
                pass

    class CartesianProducts(CartesianProductsCategory):
        """
        direct sums of modules.

        TESTS::

            sage: from yacop.categories.right_modules import YacopRightModules
            sage: D=YacopRightModules(SteenrodAlgebra(3)).CartesianProducts() ; D
            Category of Cartesian products of yacop right modules over mod 3 Steenrod algebra, milnor basis
            sage: D.super_categories()
            [Category of yacop right modules over mod 3 Steenrod algebra, milnor basis,
             Category of Cartesian products of yacop differential modules over mod 3 Steenrod algebra, milnor basis]

        """

        def extra_super_categories(self):
            return [self.base_category()]

        yacop_no_default_inheritance = 1

        def Subquotients(self):
            """
            A subobject or quotient of a direct sum is no longer a direct sum.
            This is not easy to enforce because the Sage RegressiveCovariantConstructionCategory
            concept insists that X.Subquotients() always has X as super category.
            (See `meth: RegressiveCovariantConstructionCategory.default_super_categories`)
            We achieve this through a dirty hack in our startup script.

            TESTS::

                sage: from yacop.categories.right_modules import YacopRightModules
                sage: D=YacopRightModules(SteenrodAlgebra(3)).CartesianProducts()
                sage: D in D.Subquotients().all_super_categories()
                False
                sage: from sage.categories.groups import Groups
                sage: from sage.categories.category_types import JoinCategory
                sage: J=JoinCategory((D,Groups()))
                sage: D in J.Subquotients().all_super_categories()
                False

            """
            return self.base_category().Subquotients()

        class ElementMethods:
            def _can_test_pickling(self):
                return self.parent()._can_test_pickling()

        class ParentMethods:
            def right_steenrod_action_on_basis(self, a, m):
                smds = []
                for i in range(0, len(self._sets)):
                    Mi = self._sets[i]
                    mi = self.cartesian_projection(i)(m)
                    ami = Mi.right_steenrod_action_on_basis(a, mi)
                    smds.append(self.summand_embedding(i)(ami))
                return self.sum(smds)

            def right_steenrod_action_on_basis(self, m, a):
                smds = []
                for i in range(0, len(self._sets)):
                    Mi = self._sets[i]
                    mi = self.cartesian_projection(i)(m)
                    ami = Mi.right_steenrod_action_on_basis(mi, a)
                    smds.append(self.summand_embedding(i)(ami))
                return self.sum(smds)

            def right_conj_steenrod_action_on_basis(self, a, m):
                smds = []
                for i in range(0, len(self._sets)):
                    Mi = self._sets[i]
                    mi = self.cartesian_projection(i)(m)
                    ami = Mi.right_conj_steenrod_action_on_basis(a, mi)
                    smds.append(self.summand_embedding(i)(ami))
                return self.sum(smds)

            def right_conj_steenrod_action_on_basis(self, m, a):
                smds = []
                for i in range(0, len(self._sets)):
                    Mi = self._sets[i]
                    mi = self.cartesian_projection(i)(m)
                    ami = Mi.right_conj_steenrod_action_on_basis(mi, a)
                    smds.append(self.summand_embedding(i)(ami))
                return self.sum(smds)

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

    class SuspendedObjects(SuspendedObjectsCategory):

        """
        TESTS::

            sage: import yacop.categories
            sage: C=yacop.categories.YacopRightModuleAlgebras(SteenrodAlgebra(3))
            sage: C.SuspendedObjects()
            Category of suspensions of yacop right module algebras over mod 3 Steenrod algebra, milnor basis

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

            sage: import yacop.categories
            sage: C=yacop.categories.YacopRightModuleAlgebras(SteenrodAlgebra(3))
            sage: C.TruncatedObjects()
            Category of truncations of yacop right module algebras over mod 3 Steenrod algebra, milnor basis

        """

        @cached_method
        def extra_super_categories(self):
            return [self.base_category().ModuleCategory()]

        def base_ring(self):
            return self.base_category().base_ring()

        class ParentMethods:
            pass

    class MorphismMethods:
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

    class Homsets(HomsetsCategory):
        """
        TESTS::

            sage: from yacop.categories import *
            sage: C = YacopRightModules(SteenrodAlgebra(3))
            sage: C.Homsets()
            Category of homsets of yacop right modules over mod 3 Steenrod algebra, milnor basis
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
                "disabled test method"
                pass

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

                def lam(i):
                    return self(M.monomial(i)).suspend(**kwopts)

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
             sage: C = YacopRightModuleAlgebras(SteenrodAlgebra(11))
             sage: D = YacopRightModules(SteenrodAlgebra(11))
             sage: C.Subquotients()
             Category of subquotients of yacop right module algebras over mod 11 Steenrod algebra, milnor basis
             sage: D.Subquotients()
             Category of subquotients of yacop right modules over mod 11 Steenrod algebra, milnor basis
        """

        def _repr_object_names(self):
            return "subquotients of %s" % self.base_category()._repr_object_names()

        @cached_method
        def super_categories(self):
            """
            A subquotient should again be a Steenrod algebra module, but not an algebra.

            TESTS::

               sage: from yacop.categories import *
               sage: C = YacopRightModules(SteenrodAlgebra(3))
               sage: D = C.Subquotients() ; D
               Category of subquotients of yacop right modules over mod 3 Steenrod algebra, milnor basis
               sage: C in D.all_super_categories()
               True
               sage: E = YacopRightModuleAlgebras(SteenrodAlgebra(3))
               sage: F = E.Subquotients() ; F
               Category of subquotients of yacop right module algebras over mod 3 Steenrod algebra, milnor basis
               sage: C in F.all_super_categories()
               True
               sage: E in F.all_super_categories()
               False

            """
            return [self.base_category().ModuleCategory()]

        def Subquotients(self):
            """
            Subquotients of subquotients should still be subquotients

            TESTS::

                sage: from yacop.categories.right_modules import YacopRightModules
                sage: Y=YacopRightModules(SteenrodAlgebra(2))
                sage: Y.Subquotients().Subquotients()
                Category of subquotients of yacop right modules over mod 2 Steenrod algebra, milnor basis

            """
            return self

        class ParentMethods:
            """
            The Steenrod action on a subquotient is induced from the original module.
            """

            def right_steenrod_action_on_basis(self, a, m):
                amb = self.ambient()
                return self.retract(amb.right_steenrod_action_on_basis(a, self.lift(m)))

            def right_steenrod_action_on_basis(self, m, a):
                amb = self.ambient()
                return self.retract(amb.right_steenrod_action_on_basis(self.lift(m), a))

            def right_conj_steenrod_action_on_basis(self, a, m):
                amb = self.ambient()
                return self.retract(
                    amb.right_conj_steenrod_action_on_basis(a, self.lift(m))
                )

            def right_conj_steenrod_action_on_basis(self, m, a):
                amb = self.ambient()
                return self.retract(
                    amb.right_conj_steenrod_action_on_basis(self.lift(m), a)
                )

            def lift(self, elem):
                """
                Lift an element of ``self`` to ``self.ambient()`` as per ``Subquotients`` category.

                This default implementation delegates its work to self._lift_homogeneous.
                """
                ans = []
                for (deg, smd) in elem.homogeneous_decomposition().items():
                    ans.append(self._lift_homogeneous(deg, smd))
                return self.parent().ambient().sum(ans)

            def retract(self, elem):
                """
                Retract an element of ``self.ambient()`` to ``self`` as per ``Subquotients`` category.

                This default implementation delegates its work to self._retract_homogeneous.
                """
                ans = []
                for (deg, smd) in elem.homogeneous_decomposition().items():
                    ans.append(self._retract_homogeneous(deg, smd))
                return self.parent().sum(ans)

    class SubcategoryMethods:
        pass

@yacop_category(right_action=True, is_algebra=True, module_category=YacopRightModules)
class YacopRightModuleAlgebras(Category_over_base_ring):
    def super_categories(self):
        """
        TESTS::

            sage: from yacop.categories import *
            sage: YacopRightModuleAlgebras(SteenrodAlgebra(5)).super_categories()
            [Category of yacop right modules over mod 5 Steenrod algebra, milnor basis,
             Category of algebras with basis over Finite Field of size 5]

        """
        return [self.ModuleCategory(), AlgebrasWithBasis(self.base_ring().base_ring())]

    class ParentMethods:
        pass

    class ElementMethods:
        pass

    def is_subcategory(self, c):
        if isinstance(c,YacopRightModules) and steenrod_algebra_intersect((c.base_ring(),self.base_ring())) is c.base_ring():
            return True
        return super().is_subcategory(c)

    # fixme: is it right to add these functor categories ?

    class SuspendedObjects(SuspendedObjectsCategory):
        def _repr_object_names(self):
            return "suspensions of %s" % self.base_category()._repr_object_names()

        def extra_super_categories(self):
            return []

    class Subquotients(SubquotientsCategory):
        def _repr_object_names(self):
            return "subquotients of %s" % self.base_category()._repr_object_names()

        def extra_super_categories(self):
            return []

        def super_categories(self):
            # subquotients of algebras (computed in modules) are not algebras
            return [self.base_category().ModuleCategory().Subquotients()]

    class CartesianProducts(YacopRightModules.CartesianProducts):
        pass

    class xxCartesianProducts(CartesianProductsCategory):
        def _repr_object_names(self):
            return (
                "Cartesian products of %s" % self.base_category()._repr_object_names()
            )

        def extra_super_categories(self):
            return [self.base_category().ModuleCategory()]

        def super_categories(self):
            """
            We override the default super_categories method because Sage will
            otherwise pretend that cartesian_products of Steenrod algebra algebras
            are themselves algebras.

            Among other things, this would add the Rings._Hom_ method in front of
            our customized version.

            TESTS::

                sage: from yacop.categories import *
                sage: D=YacopRightModuleAlgebras(SteenrodAlgebra(3)).CartesianProducts() ; D
                Category of Cartesian products of yacop right module algebras over mod 3 Steenrod algebra, milnor basis
                sage: D.super_categories()
                [Category of Cartesian products of yacop right modules over mod 3 Steenrod algebra, milnor basis]

            """
            return [
                self.base_category().ModuleCategory().CartesianProducts(),
            ]

    class TensorProducts(TensorProductsCategory):
        def _repr_object_names(self):
            return "tensor products of %s" % self.base_category()._repr_object_names()

        def extra_super_categories(self):
            return []

    class DualObjects(DualObjectsCategory):
        def _repr_object_names(self):
            return "duals of %s" % self.base_category()._repr_object_names()

        def extra_super_categories(self):
            return []

    class TruncatedObjects(TruncatedObjectsCategory):
        def _repr_object_names(self):
            return "truncations of %s" % self.base_category()._repr_object_names()

        def extra_super_categories(self):
            return []

    class Homsets(HomsetsCategory):
        def _repr_object_names(self):
            return "homsets of %s" % self.base_category()._repr_object_names()

        def extra_super_categories(self):
            return [
                self.base_category().ModuleCategory().Homsets(),
            ]

    class SubcategoryMethods:
        pass

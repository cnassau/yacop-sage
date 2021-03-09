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
#pylint: disable=E0213

from sage.misc.lazy_import import LazyImport, lazy_import
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
from yacop.categories.functors import SuspendedObjectsCategory
from yacop.categories.functors import TruncatedObjectsCategory
from sage.misc.cachefunc import cached_function
from sage.misc.classcall_metaclass import typecall, ClasscallMetaclass
from yacop.categories.functors import suspension
from sage.misc.lazy_attribute import lazy_attribute
from sage.rings.all import GF
from sage.categories.homset import Homset
from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra

from yacop.categories.differential_modules import YacopDifferentialModules
from yacop.categories.graded_objects import YacopGradedObjects
from yacop.categories.utils import SteenrodAlgebraAction, steenrod_antipode
from yacop.categories.utils import category_meet
import operator

class YacopBiModules(Category_over_base_ring):
    """
    The category of Yacop modules over the Steenrod algebra.

    EXAMPLES::

        sage: from yacop.categories import *
        sage: YacopBiModules(SteenrodAlgebra(7))
        Category of yacop bimodules over mod 7 Steenrod algebra, milnor basis
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

    def ModuleCategory(self):
        """
        Forget the algebra structure if present:

        TESTS::

           sage: from yacop.categories import *
           sage: YacopBiModuleAlgebras(SteenrodAlgebra(3)).ModuleCategory() is YacopBiModules(SteenrodAlgebra(3))
           True

        """
        return self


    @cached_method
    def _meet_(self, other):
        return category_meet(self,other)

    def __contains__(self, x):
        """
        a hacked, hopefully safer way to test membership. the default implementation
        fails for us - we might be doing something unexpected/wrong somewhere. without this
        hack the following fails::

            sage: from yacop.modules.projective_spaces import RealProjectiveSpace
            sage: from yacop.categories.functors import suspension
            sage: M=RealProjectiveSpace()
            sage: S=suspension(M,s=2)
            sage: X=cartesian_product((S,S))
            sage: SC = S.category()
            sage: XC = X.category()
            sage: MC = SC._meet_(XC)
            sage: [S in cat for cat in [SC, XC, MC]]
            [True, False, True]
            sage: [X in cat for cat in [SC, XC, MC]]
            [False, True, True]
        """
        ans = super(YacopBiModules, self).__contains__(x)
        if not ans:
            ans = self in x.categories()
        return ans

    def _repr_object_names(self):
        """
        TESTS::

            sage: from yacop.categories import YacopBiModules
            sage: A2 = SteenrodAlgebra(2,profile=(3,2,1))
            sage: A2.rename("A2")
            sage: YacopBiModules(A2)
            Category of yacop bimodules over A2
        """
        return "yacop bimodules over %s" % (self.base_ring())

    @cached_method
    def is_subcategory(self, other):
        """
        Subcategory detection was broken by Trac #16618. This is a hack to fix some of those problems.

        TESTS::

            sage: from yacop.categories import *
            sage: YacopBiModules(SteenrodAlgebra(2)).is_subcategory(ModulesWithBasis(GF(2)))
            True

        """
        for scat in self.super_categories():
            if scat.is_subcategory(other):
                return True
        return super(YacopBiModules, self).is_subcategory(other)

    @cached_method
    def super_categories(self):
        """
        TESTS::

            sage: from yacop.categories import *
            sage: YacopLeftModules(SteenrodAlgebra(2)).is_subcategory(ModulesWithBasis(GF(2)))
            True

        """
        from sage.categories.modules_with_basis import ModulesWithBasis
        R = self.base_ring()
        x = []
        x.append(YacopDifferentialModules(R))
        x.append(ModulesWithBasis(R.base_ring()))
        x.append(LeftModules(R))
        return x

    _is_yacop_module_category = True

    class ParentMethods:

        def __init_extra__(self):
            # register actions
            Y = self.__yacop_category__()
            self._yacop_base_ring = Y.base_ring()
            if Y._is_left:
                self.register_action(SteenrodAlgebraAction(
                    Y.base_ring(), self, self.left_steenrod_action_on_basis, is_left=True))
                self.register_action(SteenrodAlgebraAction(Y.base_ring(), self, self.left_conj_steenrod_action_on_basis,
                                                            is_left=True, op=operator.mod))
            if Y._is_right:
                self.register_action(SteenrodAlgebraAction(
                    Y.base_ring(), self, self.right_steenrod_action_on_basis, is_left=False))
                self.register_action(SteenrodAlgebraAction(Y.base_ring(), self, self.right_conj_steenrod_action_on_basis,
                                                            is_left=False, op=operator.mod))


        @abstract_method(optional=True)
        def left_steenrod_action_milnor(self, ak, mk):
            """
            Compute the LEFT action a*m where ak, mk are the basis keys of monomials
            in the Milnor basis version of the Steenrod algebra, resp. the module.

            TESTS::

                sage: from yacop.categories import YacopLeftModules
                sage: class testclass(CombinatorialFreeModule):
                ....:     def __init__(self):
                ....:          CombinatorialFreeModule.__init__(self,GF(2),ZZ,category=YacopLeftModules(SteenrodAlgebra(2)))
                ....:     def left_steenrod_action_milnor(self,ak,mk):
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
        def left_steenrod_action_milnor_conj(self, ak, mk):
            """
            Compute the conjugate action conj(a)*m where ak, mk are the basis keys of
            monomials in the Milnor basis version of the Steenrod algebra, resp. the module.

            TESTS::

                sage: from yacop.categories import YacopLeftModules
                sage: class testclass(CombinatorialFreeModule):
                ....:     def __init__(self):
                ....:          CombinatorialFreeModule.__init__(self,GF(2),ZZ,category=YacopLeftModules(SteenrodAlgebra(2)))
                ....:     def left_steenrod_action_milnor_conj(self,ak,mk):
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
        def left_steenrod_action_on_basis(self):
            """
            TESTS::

                sage: from yacop.categories import YacopLeftModules
                sage: class testclass(CombinatorialFreeModule):
                ....:     def __init__(self):
                ....:          CombinatorialFreeModule.__init__(self,GF(2),ZZ,category=YacopLeftModules(SteenrodAlgebra(2)))
                ....:     def left_steenrod_action_milnor(self,ak,mk):
                ....:          print("left_steenrod_action_milnor(%s,%s)"%(ak,mk))
                ....:          return self.zero()
                ....:     def left_steenrod_action_milnor_conj(self,ak,mk):
                ....:          print("left_steenrod_action_milnor_conj(%s,%s)"%(ak,mk))
                ....:          return self.zero()
                sage: C = testclass()
                sage: Sq(3) * C.monomial(17)
                left_steenrod_action_milnor((3,),17)
                0
                sage: Sq(3) % C.monomial(17)
                left_steenrod_action_milnor_conj((3,),17)
                0
            """
            if self.left_steenrod_action_milnor is not NotImplemented:
                return self._left_action_from_milnor
            if self.left_steenrod_action_milnor_conj is not NotImplemented:
                return self._left_action_from_milnor_conj
            return NotImplemented

        @lazy_attribute
        def left_conj_steenrod_action_on_basis(self):
            if self.left_steenrod_action_milnor_conj is not NotImplemented:
                return self._left_conj_action_from_milnor_conj
            if self.left_steenrod_action_milnor is not NotImplemented:
                return self._left_conj_action_from_milnor
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

        def _left_action_from_milnor_conj(self, a, m):
            return self._action_from_milnor(self.left_steenrod_action_milnor_conj, a.antipode(), m)

        def _right_action_from_milnor_conj(self, m, a):
            return self._action_from_milnor(self.right_steenrod_action_milnor_conj, m, a.antipode())

        def _left_conj_action_from_milnor(self, a, m):
            return self._action_from_milnor(self.left_steenrod_action_milnor, a.antipode(), m)

        def _right_conj_action_from_milnor(self, m, a):
            return self._action_from_milnor(self.right_steenrod_action_milnor, m, a.antipode())

        # direct implementations of actions and conjugate actions

        def _left_action_from_milnor(self, a, m):
            return self._action_from_milnor(self.left_steenrod_action_milnor, a.milnor(), m)

        def _right_action_from_milnor(self, m, a):
            return self._action_from_milnor(self.right_steenrod_action_milnor, m, a.milnor())

        def _left_conj_action_from_milnor_conj(self, a, m):
            return self._action_from_milnor(self.left_steenrod_action_milnor_conj, a.milnor(), m)

        def _right_conj_action_from_milnor_conj(self, m, a):
            return self._action_from_milnor(self.right_steenrod_action_milnor_conj, m, a.milnor())

        def _action_from_milnor(self, actfunc, a, m):
            adct = a.monomial_coefficients()
            mdct = m.monomial_coefficients()
            res = []
            for ak, cf1 in adct.items():
                for mk, cf2 in mdct.items():
                    d = actfunc(ak, mk)
                    res.append((d, cf1*cf2))
            return self.linear_combination(res)

        def _manual_test_left_action(self, reg, opdeg=None, verbose=False):
            return self._manual_test_action(reg, opdeg=opdeg, mode='left', verbose=verbose)

        def _manual_test_right_action(self, reg, opdeg=None, verbose=False):
            return self._manual_test_action(reg, opdeg=opdeg, mode='right', verbose=verbose)

        def _manual_test_bimod_action(self, reg, opdeg=None, verbose=False):
            return self._manual_test_action(reg, opdeg=opdeg, mode='bimod', verbose=verbose)

        def _manual_test_left_conj_action(self, reg, opdeg=None, verbose=False):
            return self._manual_test_action(reg, opdeg=opdeg, mode='leftconj', verbose=verbose)

        def _manual_test_right_conj_action(self, reg, opdeg=None, verbose=False):
            return self._manual_test_action(reg, opdeg=opdeg, mode='rightconj', verbose=verbose)

        def _manual_test_bimod_conj_action(self, reg, opdeg=None, verbose=False):
            return self._manual_test_action(reg, opdeg=opdeg, mode='bimodconj', verbose=verbose)

    class ElementMethods:
        pass

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

            def left_steenrod_action_on_basis(self, a, elem):
                return self.linear_combination((self.monomial(tuple(k)), c)
                                               for (k, c) in self.__act_left(a, self._sets, elem))

            def right_steenrod_action_on_basis(self, elem, a):
                return self.linear_combination((self.monomial(tuple(k)), c)
                                               for (k, c) in self.__act_right(elem, self._sets, a))

            def left_conj_steenrod_action_on_basis(self, a, elem):
                return self.linear_combination((self.monomial(tuple(k)), c)
                                               for (k, c) in self.__act_left_conj(a, self._sets, elem))

            def right_conj_steenrod_action_on_basis(self, elem, a):
                return self.linear_combination((self.monomial(tuple(k)), c)
                                               for (k, c) in self.__act_right_conj(elem, self._sets, a))

            def __act_left(self, a, parents, elem):
                for (key, cf) in elem:
                    M0 = parents[0]
                    m0 = M0._from_dict({key[0]: cf})
                    if len(parents) == 1:
                        for (k, c) in M0.left_steenrod_action_on_basis(a, m0):
                            yield [k, ], c
                    else:
                        A = a.parent()
                        cop = a.coproduct()
                        for ((k1, k2), acf) in cop:
                            a1 = A._from_dict({k1: acf})
                            a2 = A.monomial(k2)
                            deg2 = a2.degree()
                            for (k1, c1) in M0.left_steenrod_action_on_basis(a1, m0):
                                for (k, c) in self.__act_left(a2, parents[1:], [(key[1:], c1), ]):
                                    if (deg2 & 1) and (m0.e & 1):
                                        c = -c
                                    yield [k1, ]+k, c

            def __act_right(self, elem, parents, a):
                ln = len(parents)-1
                for (key, cf) in elem:
                    M0 = parents[ln]
                    m0 = M0._from_dict({key[ln]: cf})
                    if len(parents) == 1:
                        for (k, c) in M0.right_steenrod_action_on_basis(m0, a):
                            yield [k, ], c
                    else:
                        A = a.parent()
                        cop = a.coproduct()
                        for ((k1, k2), acf) in cop:
                            a1 = A._from_dict({k1: acf})
                            a2 = A.monomial(k2)
                            deg1 = a1.degree()
                            for (k1, c1) in M0.right_steenrod_action_on_basis(m0, a2):
                                for (k, c) in self.__act_right([(key[:ln], c1), ], parents[:ln], a1):
                                    if (deg1 & 1) and (m0.e & 1):
                                        c = -c
                                    yield k+[k1, ], c

            def __act_left_conj(self, a, parents, elem):
                for (key, cf) in elem:
                    M0 = parents[0]
                    m0 = M0._from_dict({key[0]: cf})
                    if len(parents) == 1:
                        for (k, c) in M0.left_conj_steenrod_action_on_basis(a, m0):
                            yield [k, ], c
                    else:
                        A = a.parent()
                        cop = a.coproduct()
                        for ((k1, k2), acf) in cop:
                            a1 = A._from_dict({k1: acf})
                            a2 = A.monomial(k2)
                            deg2 = a2.degree()
                            for (k1, c1) in M0.left_conj_steenrod_action_on_basis(a1, m0):
                                for (k, c) in self.__act_left_conj(a2, parents[1:], [(key[1:], c1), ]):
                                    if (deg2 & 1) and (m0.e & 1):
                                        c = -c
                                    yield [k1, ]+k, c

            def __act_right_conj(self, elem, parents, a):
                ln = len(parents)-1
                for (key, cf) in elem:
                    M0 = parents[ln]
                    m0 = M0._from_dict({key[ln]: cf})
                    if len(parents) == 1:
                        for (k, c) in M0.right_conj_steenrod_action_on_basis(m0, a):
                            yield [k, ], c
                    else:
                        A = a.parent()
                        cop = a.coproduct()
                        for ((k1, k2), acf) in cop:
                            a1 = A._from_dict({k1: acf})
                            a2 = A.monomial(k2)
                            deg1 = a1.degree()
                            for (k1, c1) in M0.right_conj_steenrod_action_on_basis(m0, a2):
                                for (k, c) in self.__act_right_conj([(key[:ln], c1), ], parents[:ln], a1):
                                    if (deg1 & 1) and (m0.e & 1):
                                        c = -c
                                    yield k+[k1, ], c

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
                    c = keys[i+1:]
                    for (key, cf) in b:
                        if 0 != (i & 1):
                            cf = -cf
                        ans.append((tuple(list(a)+[key, ]+list(c)), cf))
                return self._from_dict(dict(ans))

            @staticmethod
            def SuspendedObjectsFactory(module, *args, **kwopts):
                from sage.categories.tensor import tensor
                l = len(module._sets)
                last = module._sets[l-1]
                newsets = list(module._sets[:l-1]) + \
                    [suspension(last, *args, **kwopts), ]
                return tensor(tuple(newsets))

        class ElementMethods:
            def _can_test_pickling(self):
                return self.parent()._can_test_pickling()

    class CartesianProducts(CartesianProductsCategory):
        """
        direct sums of modules.
        """

        def extra_super_categories(self):
            return []

        def super_categories(self):
            """
            Sage thinks the cartesian product of algebras is an algebra, but we disagree:

            TESTS::

                sage: from yacop.categories import *
                sage: D=YacopLeftModuleAlgebras(SteenrodAlgebra(3)).CartesianProducts() ; D
                Category of Cartesian products of LEFT Yacop module algebras over mod 3 Steenrod algebra, milnor basis
                sage: D.super_categories()
                [Category of LEFT Yacop modules over mod 3 Steenrod algebra, milnor basis,
                 Category of Cartesian products of vector spaces with basis over Finite Field of size 3,
                 Category of Cartesian products of yacop graded objects]
                sage: D=YacopRightModules(SteenrodAlgebra(3)).CartesianProducts() ; D
                Category of Cartesian products of right Yacop modules over mod 3 Steenrod algebra, milnor basis
                sage: D.super_categories()
                [Category of right Yacop modules over mod 3 Steenrod algebra, milnor basis,
                 Category of Cartesian products of vector spaces with basis over Finite Field of size 3,
                 Category of Cartesian products of yacop graded objects]

            Otherwise we'd get lots of problems with Homsets between Steenrod algebra algebras.
            """
            obj = self
            return [self.base_category().ModuleCategory(), ] + super(YacopBiModules.CartesianProducts, obj).super_categories()

        def Subquotients(self):
            """
            A subobject or quotient of a direct sum is no longer a direct sum
            """
            return self.base_category().Subquotients()

        class ElementMethods:
            def _can_test_pickling(self):
                return self.parent()._can_test_pickling()

        class ParentMethods:

            def left_steenrod_action_on_basis(self, a, m):
                smds = []
                for i in range(0, len(self._sets)):
                    Mi = self._sets[i]
                    mi = self.cartesian_projection(i)(m)
                    ami = Mi.left_steenrod_action_on_basis(a, mi)
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

            def left_conj_steenrod_action_on_basis(self, a, m):
                smds = []
                for i in range(0, len(self._sets)):
                    Mi = self._sets[i]
                    mi = self.cartesian_projection(i)(m)
                    ami = Mi.left_conj_steenrod_action_on_basis(a, mi)
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
                return "(%s)" % ", ".join(mod._repr_term(mod.cartesian_projection(i)(elem)) for (mod, i) in zip(self._sets, self._set_keys))

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
                return cartesian_product([suspension(mod, *args, **kwopts) for mod in module._sets])

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

            sage: import yacop.categories
            sage: C=yacop.categories.YacopLeftModuleAlgebras(SteenrodAlgebra(3))
            sage: C.SuspendedObjects()
            Category of suspensions of LEFT Yacop module algebras over mod 3 Steenrod algebra, milnor basis

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
            sage: C=yacop.categories.YacopLeftModuleAlgebras(SteenrodAlgebra(3))
            sage: C.TruncatedObjects()
            Category of truncations of LEFT Yacop module algebras over mod 3 Steenrod algebra, milnor basis

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
            Category of homsets of LEFT Yacop modules over mod 3 Steenrod algebra, milnor basis
        """

        def _repr_object_names(self):
            return "homsets of %s" % self.base_category()._repr_object_names()

        def extra_super_categories(self):
            # TODO: make this a Steenrod algebra module
            return [ModulesWithBasis(self.base_category().ModuleCategory().base_ring()).Homsets(), ]

        def super_categories(self):
            # TODO: make this a Steenrod algebra module
            return [ModulesWithBasis(self.base_category().ModuleCategory().base_ring()).Homsets(), ]

        class ParentMethods:
            pass

        class ElementMethods:

            def _test_nonzero_equal(self, **options):
                pass

            def kernel(self):
                M = self.domain()
                if hasattr(M, "KernelOf"):
                    return M.KernelOf(self)
                raise NotImplementedError(
                    "kernel of map from %s not implemented" % M)

            def image(self):
                N = self.codomain()
                if hasattr(N, "ImageOf"):
                    return N.ImageOf(self)
                raise NotImplementedError(
                    "image of map into %s not implemented" % N)

            def cokernel(self):
                N = self.codomain()
                if hasattr(N, "CokernelOf"):
                    return N.CokernelOf(self)
                raise NotImplementedError(
                    "cokernel of map into %s not implemented" % N)

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
                def lam(i): return self(M.monomial(i)).suspend(**kwopts)
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
             Category of subquotients of LEFT Yacop module algebras over mod 11 Steenrod algebra, milnor basis
             sage: D.Subquotients()
             Category of subquotients of LEFT Yacop modules over mod 11 Steenrod algebra, milnor basis
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
               Category of subquotients of LEFT Yacop modules over mod 3 Steenrod algebra, milnor basis
               sage: C in D.all_super_categories()
               True
               sage: E = YacopLeftModuleAlgebras(SteenrodAlgebra(3))
               sage: F = E.Subquotients() ; F
               Category of subquotients of LEFT Yacop module algebras over mod 3 Steenrod algebra, milnor basis
               sage: C in F.all_super_categories()
               True
               sage: E in F.all_super_categories()
               False

            """
            return [self.base_category().ModuleCategory()]

        class ParentMethods:
            """
            The Steenrod action on a subquotient is induced from the original module.
            """

            def left_steenrod_action_on_basis(self, a, m):
                amb = self.ambient()
                return self.retract(amb.left_steenrod_action_on_basis(a, self.lift(m)))

            def right_steenrod_action_on_basis(self, m, a):
                amb = self.ambient()
                return self.retract(amb.right_steenrod_action_on_basis(self.lift(m), a))

            def left_conj_steenrod_action_on_basis(self, a, m):
                amb = self.ambient()
                return self.retract(amb.left_conj_steenrod_action_on_basis(a, self.lift(m)))

            def right_conj_steenrod_action_on_basis(self, m, a):
                amb = self.ambient()
                return self.retract(amb.right_conj_steenrod_action_on_basis(self.lift(m), a))

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

class YacopBiModuleAlgebras(Category_over_base_ring):

    def ModuleCategory(self):
        """
        Forget the algebra structure if present:

        TESTS::

           sage: from yacop.categories import *
           sage: YacopBiModuleAlgebras(SteenrodAlgebra(3)).ModuleCategory() is YacopBiModules(SteenrodAlgebra(3))
           True

        """
        return YacopBiModules(self.base_ring())

    def super_categories(self):
        """
        TESTS::

            sage: from yacop.categories import *
            sage: YacopBiModuleAlgebras(SteenrodAlgebra(5)).super_categories()
        """
        return [self.ModuleCategory(), AlgebrasWithBasis(self.base_ring().base_ring())]


    def __contains__(self, x):
        """
        a hacked, hopefully safer way to test membership. the default implementation
        fails for us - we might be doing something unexpected/wrong somewhere. without this
        hack the following fails::

            sage: from yacop.modules.projective_spaces import RealProjectiveSpace
            sage: M=RealProjectiveSpace()
            sage: M.category()
            Category of yacop left module algebras over mod 2 Steenrod algebra, milnor basis
            sage: M in M.category()
            True

        """
        ans = super(YacopBiModuleAlgebras, self).__contains__(x)
        if not ans:
            ans = self in x.categories()
        return ans

    @cached_method
    def is_subcategory(self, other):
        """
        Subcategory detection was broken by Trac #16618. This is a hack to fix some of those problems.

        TESTS::

            sage: from yacop.categories import *
            sage: YacopBiModules(SteenrodAlgebra(2)).is_subcategory(ModulesWithBasis(GF(2)))
            True

        """
        for scat in self.super_categories():
            if scat.is_subcategory(other):
                return True
        return super(YacopBiModuleAlgebras, self).is_subcategory(other)

    class ParentMethods:
        pass

    class ElementMethods:
        pass

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

    class CartesianProducts(CartesianProductsCategory):

        def _repr_object_names(self):
            return "cartesian products of %s" % self.base_category()._repr_object_names()

        def extra_super_categories(self):
            return []

        def super_categories(self):
            """
            We override the default super_categories method because Sage will
            otherwise pretend that cartesian_products of Steenrod algebra algebras
            are themselves algebras.

            Among other things, this would add the Rings._Hom_ method in front of
            our customized version.
            """
            return [self.base_category().ModuleCategory().CartesianProducts()]

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
            return []



# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

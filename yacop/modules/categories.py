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

class YacopGradedSets(Category_singleton):
    """
    Category of sets with a (t,e,s)-grading.

    """

    def _repr_object_names(self):
       return "yacop graded sets"

    def super_categories(self):
       from sage.categories.objects import Objects
       return [Objects()]

    class ParentMethods:

       @abstract_method(optional=False)
       def bbox(self):
          """
          Return a bounding box of ``self``.
          """

       @abstract_method(optional=False)
       def _truncate_region(self,reg):
          """
          Return the subset of ``self`` corresponding to the region ``reg``.
          """

       def truncate(self,reg=None,**kwargs):
          if reg is None:
             reg = region(**kwargs)
          return self._truncate_region(reg)

       @abstract_method(optional=False)
       def degree(self,elem):
          """
          Return the degree of the element ``elem`` as a region object.
          """

       def nontrivial_degrees(self,reg):
          """
          Return an iterator for the nontrivial degrees in the given region.
          """
          # TODO: write a smarter implementation that divides the region and uses
          # the bounding boxes.
          def walker(X):
              dct = dict()
              for g in X:
                  dg = self.degree(g)
                  if dg not in dct:
                      dct[dg]=1
                      yield dg
          return walker(self._truncate_region(reg))

    class ElementMethods:
        pass

class YacopObjects(Category_singleton):
    """
    A helper category to declare functorial constructions for Yacop graded objects.
    """

    def _repr_object_names(self):
       return "yacop graded objects"

    def super_categories(self):
       from sage.categories.objects import Objects
       """
       The right thing to return would be 'Objects()', but that doesn't have Subquotients and CartesianProducts.
       Likewise, 'Sets()' doesn't have TensorProducts... which we're changing below
       """
       return [Objects(),]

    class ParentMethods:
        def cartesian_product(*parents):
            return parents[0].CartesianProduct(
                parents,
                category = cartesian_product.category_from_parents(parents))

    class SubcategoryMethods:

        @cached_method
        def CartesianProducts(self):
            return CartesianProductsCategory.category_of(self)

        @cached_method
        def Subquotients(self):
            return SubquotientsCategory.category_of(self)

        @cached_method
        def TensorProducts(self):
            return TensorProductsCategory.category_of(self)

class YacopGradedObjects(Category_singleton):
    """
    Category of pairs (M,G) where G is a Grading

    EXAMPLES::

        sage: from yacop.modules.categories import *
        sage: from yacop import *
        sage: X = YacopGradedObjects().example() ; X
        {1, ..., 18}
        sage: X.grading()
        mod 7 decomposition of the range {1, ..., 18}
        sage: X.graded_basis((3,))
        [3, 10, 17]
        sage: Y = suspension(X,offset=3) ; Y
        suspension with offset 3 of mod 7 decomposition of the range {1, ..., 18}
        sage: Y.graded_basis((3,))
        [7, 14]
        sage: X.degree(10)
        3
        sage: X.bbox()  # bounding box
        {0, ..., 6}
    """

    def _repr_object_names(self):
       return "yacop graded objects"

    def super_categories(self):
       return [YacopObjects(),]

    def example(self):
        """
        Example of a GradedObject: IntegerRange {1,...,18} with mod 7 decomposition

        TESTS::

            sage: from yacop.modules.categories import *
            sage: YacopGradedObjects().example().grading()
            mod 7 decomposition of the range {1, ..., 18}
        """

        from yacop.utils.gradings import SampleGrading
        from sage.sets.integer_range import IntegerRange, IntegerRangeFinite
        from sage.rings.integer import Integer
        class GradedRange(IntegerRangeFinite):

          def __init__(self,a,b,modulus,category=None):
             if category is None:
                category = YacopGradedObjects()
             IntegerRangeFinite.__init__(self,Integer(a),Integer(b))
             self._refine_category_(category)
             self._yacop_ref = self
             self._yacop_grading = SampleGrading(self._yacop_ref,modulus)
             #self.rename(self._yacop_grading._format_(IntegerRange(Integer(a),Integer(b))))

          class Element(Integer):
             pass

          # must replace element_class because suspension wraps Element._repr_
          # and Integer._repr_ can't be replaced
          element_class = Element

        class GradedRange_SuspendedObjects(GradedRange):
             pass

        GradedRange.SuspendedObjects = GradedRange_SuspendedObjects

        return GradedRange(1,19,7)

    class ParentMethods:

        def degree(self,element):
            """
            Return the degree of element with respect to the current grading
            """
            return self._yacop_grading.degree(element)

        def bbox(self):
            """
            Return a bounding box
            """
            return self._yacop_grading.bbox()

        def __region(self,reg2,**kwargs):
            if not reg2 is None and not isinstance(reg2,region):
               # might be dealing with a sample grading
               return reg2
            reg = region(**kwargs)
            if not reg2 is None:
                reg = reg2.intersect(reg)
            return reg

        def graded_basis(self,region=None,**kwargs):
            """
            Return the basis of this module in the given region.
            """
            return self._yacop_grading.basis(self.__region(region,**kwargs))

        def graded_basis_coefficients(self,elem,region=None,**kwargs):
            """
            Return the decomposition of ``elem`` with respect to the graded basis of this region.
            """
            return self._yacop_grading.basis_coefficients(elem,self.__region(region,**kwargs))

        def nontrivial_degrees(self,region=None,**kwargs):
            """
            Return the nontrivial degrees of this module in the given region.
            """
            return self._yacop_grading.nontrivial_degrees(self.__region(region,**kwargs))

        def dimension(self,region=None,**kwargs):
            """
            Return the vector space dimension of this module in the given region.
            """
            try:
               return len(self.graded_basis(self.__region(region,**kwargs)))
            except:
               return +Infinity

        def grading(self):
            """
            Return the Gradings() object that implements the grading of `self`.

            EXAMPLES::

                sage: from yacop.modules.categories import *
                sage: YacopGradedObjects().example().grading()
                mod 7 decomposition of the range {1, ..., 18}

            """
            return self._yacop_grading

        def _some_homogeneous_elements(self):
            el = self.an_element()
            if hasattr(el,"homogeneous_decomposition"):
                sp = el.homogeneous_decomposition()
                return sp.items()
            try:
                dg = self.degree(el)
                return [(dg,el)]
            except:
                raise NotImplementedError

        def _set_grading(self,grading):
            """
            Set the grading and register `self` as the ungraded original module.
            """
            self._yacop_ref = self
            self._yacop_grading = grading

        def _test_yacop_grading(self,tester = None,**options):
            from sage.misc.sage_unittest import TestSuite
            from sage.misc.lazy_format import LazyFormat
            from sage.categories.enumerated_sets import EnumeratedSets
            from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
            is_sub_testsuite = (tester is not None)
            tester = self._tester(tester = tester, **options)

            if hasattr(self.grading(),"_domain"):
                tester.assertTrue(self is self.grading()._domain,
                                  LazyFormat("grading of %s has wrong _domain attribute %s")%(self,self.grading()._domain))

            bbox = self.bbox()
            tester.assertTrue(bbox.__class__ == region,
                              LazyFormat("bounding box of %s is not a region")%(self,))

            # make sure we can get a basis of the entire module
            basis = self.graded_basis()
            tester.assertTrue(basis in EnumeratedSets(),
                              LazyFormat("graded basis of %s is not an EnumeratedSet")%(self,))

            # nontrivial_degrees
            ntdegs = self.nontrivial_degrees()
            tester.assertTrue(basis in EnumeratedSets(),
                              LazyFormat("nontrivial_degrees of %s is not an EnumeratedSet")%(self,))

            # check whether a presumably finite piece is also an EnumeratedSet
            rg = region(tmax=10,tmin=-10,smax=10,smin=-10,emax=10,emin=-10)
            basis = self.graded_basis(rg)
            tester.assertTrue(basis in EnumeratedSets(),
                              LazyFormat("graded basis of %s in the region %s is not an EnumeratedSet")%(self,rg))

            for (deg,elem) in self._some_homogeneous_elements():
                deg2 = self.degree(elem)
                if hasattr(elem,"degree"):
                    deg3 = elem.degree()
                    tester.assertEqual(deg2,deg3,
                                       LazyFormat("parent.degree(el) != (el).degree() for parent %s and element %s")
                                       %(self,elem))

                tester.assertEqual(deg2,deg,
                                   LazyFormat("homogeneuous_decomposition claims %s has degree %s, but degree says %s")
                                   %(elem,deg,deg2))

                # test graded_basis_coefficients
                b = self.grading().basis(deg)
                tester.assertTrue(b.cardinality() < Infinity,
                                  LazyFormat("%s not finite in degree %s")%(self,deg))

            from sage.categories.commutative_additive_groups import CommutativeAdditiveGroups
            if self in CommutativeAdditiveGroups():
                el = self.an_element()
                sp = el.homogeneous_decomposition()
                for (deg,elem) in sp.items():
                    b = self.grading().basis(deg)
                    c = self.graded_basis_coefficients(elem,deg)
                    sm = sum(cf*be for (cf,be) in zip(c,b))
                    if elem != sm:
                        print("self=",self)
                        print("elem=",elem)
                        print("deg=",deg)
                        print("graded basis=",list(b))
                        print("lhs=",elem.monomial_coefficients())
                        print("rhs=",sm.monomial_coefficients())
                    tester.assertEqual(elem,sm,
                                       LazyFormat("graded_basis_coefficients failed on element %s of %s: sums to %s")
                                       %(elem,self,sm))

                el2 = sum(smd for (key,smd) in sp.items())
                tester.assertEqual(el.parent(),el2.parent(),
                                   LazyFormat("%s and the sum of its homogeneous pieces have different parents:\n   %s\n!= %s")
                                   %(el,el.parent(),el2.parent(),))
                if el.parent() is el2.parent():
                    tester.assertEqual(el,el2,
                                       LazyFormat("%s is not the sum of its homogeneous pieces (which is %s)")%(el,el2,))



        def suspend_element(self,elem,**kwargs):
            from copy import deepcopy
            N = suspension(self,**kwargs)
            x = deepcopy(elem)
            x._set_parent(N)
            return x

    class SuspendedObjects(SuspendedObjectsCategory):

        """
        TESTS::

            sage: from yacop.modules.categories import *
            sage: Y=YacopGradedObjects()
            sage: Y.SuspendedObjects()
            Category of suspensions of yacop graded objects
        """

        def extra_super_categories(self):
            return [self.base_category()]

        class ParentMethods:
           def an_element(self):
               from copy import copy
               x = copy(self._yacop_ref.an_element())
               x._set_parent(self)
               return x

    class ElementMethods:

        def degree(self):
           """
           Degree of `self` with respect to the parent's grading.
           """
           try:
              res = self._deg
           except AttributeError:
              res = self._deg = self.parent().degree(self)
           return res

        def homogeneous_decomposition(self):
           """
           Decompose element into homogeneous components.
           """
           return self.parent().grading().split_element(self)

        def suspend(self,*args,**kwargs):
           return self.parent().suspend_element(self,*args,**kwargs)

    class SubcategoryMethods:
        pass

    class Subquotients(SubquotientsCategory):
        """
        TESTS::

            sage: from yacop.modules.categories import *
            sage: Y=YacopGradedObjects()
            sage: Y.Subquotients()
            Category of subquotients of yacop graded objects
        """

        def _repr_object_names(self):
            return "subquotients of yacop graded objects"

        def extra_super_categories(self):
            return [self.base_category()]

    class CartesianProducts(CartesianProductsCategory):

        """
        TESTS::

            sage: from yacop.modules.categories import *
            sage: Y=YacopGradedObjects()
            sage: Y.CartesianProducts()
            Category of Cartesian products of yacop graded objects
        """

        def extra_super_categories(self):
            return [self.base_category()]

        def Subquotients(self):
           """
           A subobject or quotient of a direct sum is no longer a direct sum
           """
           return self.base_category().Subquotients()

        class ElementMethods:
            pass

        class ParentMethods:

           def __init_extra__(self):
              self._yacop_grading = cartesian_product([mod._yacop_grading for mod in self._sets])
              # hack, because cartesian_product doesn't accept extra arguments
              self._yacop_grading._domain=self

    class TensorProducts(TensorProductsCategory):

        """
        TESTS::

            sage: from yacop.modules.categories import *
            sage: Y=YacopGradedObjects()
            sage: Y.TensorProducts()
            Category of tensor products of yacop graded objects
        """

        def _repr_object_names(self):
            return "tensor products of yacop graded objects"

        @cached_method
        def extra_super_categories(self):
            return [self.base_category()]

        def Subquotients(self):
           """
           A subobject or quotient of a tensor product is no longer a tensor product
           """
           return self.base_category().Subquotients()

        class ElementMethods:
            pass

        class ParentMethods:
            def __init_extra__(self):
                self._yacop_grading = tensor([mod._yacop_grading for mod in self._sets])
                # hack, because tensor doesn't accept extra arguments
                self._yacop_grading._domain=self


##################################################################################
##################################################################################
##################################################################################
##################################################################################

import sage.categories.action
import operator
class SteenrodAlgebraAction(sage.categories.action.Action):
    def __init__(self, A, M, thefunc, is_left=True, op=operator.mul):
        # if A is a subalgebra of the Steenrod algebra we nevertheless register an action
        # of the full Steenrod algebra (which raises an error in _act_ if necessary)
        self._Aeff = SteenrodAlgebra(A.prime(),generic=A.is_generic())
        sage.categories.action.Action.__init__(self, self._Aeff, M, is_left, op)
        self._module = M
        self._algebra = A
        self._thefunc = thefunc
        self._gf = A.base_ring()

    def _act_(self, a, x):
        if not self._is_left:
            a, x = x, a
        if a in self._gf:
            return self._module._scalar_action(a,x)
        if not self._Aeff is self._algebra:
            a = self._algebra(a) 
        return self._thefunc(a,x)

@cached_function
def steenrod_antipode(x):
    """
    a cached version of the antipode for testing purposes
    """
    return x.antipode()

class SteenrodAlgebraModules(Category_over_base_ring):
    """
    The category of Yacop modules over the Steenrod algebra.

    EXAMPLES::

        sage: from yacop.modules.categories import *
        sage: SteenrodAlgebraModules(SteenrodAlgebra(7),is_right=True,is_left=False)
        Category of right Yacop modules over mod 7 Steenrod algebra, milnor basis
    """

    @staticmethod
    def __classcall_private__(cls,R,is_left=None,is_right=None,is_bimod=None,is_algebra=None):
       if is_left is None: is_left=False
       if is_right is None: is_right=False
       if is_bimod is None: is_bimod=False
       if is_algebra is None: is_algebra=False
       if is_bimod:
           is_left = True
           is_right = True
       return super(cls,SteenrodAlgebraModules).__classcall__(cls,R,is_left,is_right,is_bimod,is_algebra)

    def __init__(self,R,is_left,is_right,is_bimod,is_algebra):
        self._R = R
        self._is_left, self._is_right, self._is_bimod, self._is_algebra = is_left, is_right, is_bimod, is_algebra
        Category_over_base_ring.__init__(self,R)

        # hack to tell __init_extra__ which actions to register
        def func(xxx):
            return self
        func.__name__ = "__yacop_category__"
        #setattr(self.ParentMethods,func.__name__,func)

    def an_instance(self):
        """
        EXAMPLE::

            sage: from yacop.modules.categories import *
            sage: YacopLeftModules(SteenrodAlgebra(2)).an_instance()
            mod 2 cohomology of real projective space P^{+Infinity}
            sage: YacopLeftModules(SteenrodAlgebra(5)).an_instance()
            mod 5 cohomology of the classifying space of ZZ/5ZZ
        """
        from yacop.modules.all import RealProjectiveSpace, BZp
        if self._R.is_generic():
            return BZp(self._R.characteristic())
        else:
            return RealProjectiveSpace()

    def ModuleCategory(self):
       """
       Forget the algebra structure if present:

       TESTS::

          sage: from yacop.modules.categories import *
          sage: YacopRightModuleAlgebras(SteenrodAlgebra(3)).ModuleCategory() is YacopRightModules(SteenrodAlgebra(3))
          True

       """
       if self._is_bimod:
           return YacopBiModules(self._R)
       elif self._is_right:
           return YacopRightModules(self._R)
       else:
           return YacopLeftModules(self._R)

    @cached_method
    def _meet_(self,other):
        from yacop.modules.categories import steenrod_algebra_intersect
        try:
            oR = other._R
            R = steenrod_algebra_intersect((self._R,oR))
        except: 
            return super(SteenrodAlgebraModules,self)._meet_(other)
        
        is_algebra = self._is_algebra and other._is_algebra
        is_bimod   = self._is_bimod   and other._is_bimod
        is_right   = self._is_right   and other._is_right
        is_left    = self._is_left    and other._is_left
        
        if is_algebra:
            if is_bimod:
                return YacopBiModuleAlgebras(R)
            elif is_right:
                return YacopRightModuleAlgebras(R)
            else:
                return YacopLeftModuleAlgebras(R)
        else:
            if is_bimod:
                return YacopBiModules(R)
            elif is_right:
                return YacopRightModules(R)
            else:
                return YacopLeftModules(R)
                
    def __contains__(self,x):
        """
        a hacked, hopefully safer way to test membership. the default implementation
        fails for us - we might be doing something unexpected/wrong somewhere. without this
        hack the following fails::

            sage: from yacop.modules.projective_spaces import RealProjectiveSpace
            sage: from yacop.modules.functors import suspension
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
        ans = super(SteenrodAlgebraModules, self).__contains__(x)
        if not ans:
            ans = self in x.categories()
        return ans

    def _repr_object_names(self):

        if self._is_left:
            if self._is_right:
                x = "left and right Yacop module"
            else:
                x = "left Yacop module"
        else:
            if self._is_right:
                x = "right Yacop module"
            else:
                x = "Yacop module"
        if self._is_bimod:
            x = "Yacop bimodule"

        if self._is_algebra:
           x = "%s algebras" % x
        else:
           x = "%ss" % x

        return "%s over %s" % (x,self._R)

    @cached_method
    def is_subcategory(self,other):
        """
        Subcategory detection was broken by Trac #16618. This is a hack to fix some of those problems.

        TESTS::

            sage: from yacop.modules.categories import *
            sage: YacopLeftModules(SteenrodAlgebra(2)).is_subcategory(ModulesWithBasis(GF(2)))
            True

        """
        for scat in self.super_categories():
            if scat.is_subcategory(other):
                return True
        return super(SteenrodAlgebraModules,self).is_subcategory(other)

    @cached_method
    def super_categories(self):
        """
        TESTS::

            sage: from yacop.modules.categories import *
            sage: YacopLeftModules(SteenrodAlgebra(2)).is_subcategory(ModulesWithBasis(GF(2)))
            True

        """
        from sage.categories.modules_with_basis import ModulesWithBasis
        R = self.base_ring()
        x = []
        if self._is_algebra:
            x.append(AlgebrasWithBasis(R.base_ring()))
            x.append(self.ModuleCategory())
        else:
            x.append(ModulesWithBasis(R.base_ring()))
        if self._is_bimod:
            #x.append(Bimodules(R,R))
            x.append(YacopLeftModules(R))
            x.append(YacopRightModules(R))
        else:
            if self._is_right:
                x.append(RightModules(R))
            if self._is_left:
                x.append(LeftModules(R))
        x.append(YacopGradedObjects())
        return x

    class ParentMethods:

        @cached_method
        def __yacop_category__(self):
            for cat in self.categories():
               if isinstance(cat,SteenrodAlgebraModules):
                  return cat
            raise ValueError, "internal error: cannot detect yacop category"

        def __init_extra__(self):
            # register actions
            Y = self.__yacop_category__()
            self._yacop_base_ring = Y.base_ring()
            if Y._is_left:
                self.register_action(SteenrodAlgebraAction(Y._R,self,self.left_steenrod_action_on_basis,is_left=True))
                self.register_action(SteenrodAlgebraAction(Y._R,self,self.left_conj_steenrod_action_on_basis,
                                                           is_left=True, op=operator.mod))
            if Y._is_right:
                self.register_action(SteenrodAlgebraAction(Y._R,self,self.right_steenrod_action_on_basis,is_left=False))
                self.register_action(SteenrodAlgebraAction(Y._R,self,self.right_conj_steenrod_action_on_basis,
                                                           is_left=False, op=operator.mod))


        def _test_steenrod_action(self,tester=None,**options):
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
                    tester.assertEqual(y,steenrod_antipode(e)%x,
                                        LazyFormat("conjugate action check failed: e.antipode()%x != e*x for x=%s, e=%s")
                                        % (x,e))
                if Y._is_right:
                    y = x*e        # does right action work?
                    tester.assertEqual(y,x%steenrod_antipode(e),
                                        LazyFormat("conjugate action check failed: x%e.antipode() != x*e for x=%s, e=%s")
                                        % (x,e))
                if Y._is_bimod:
                    tester.assertEqual((e*x)*e,e*(x*e),
                                    LazyFormat("bimodule check failed: (ex)e != e(xe) for x=%s, e=%s")
                                    % (x,e))
            if False:
               tester.assertTrue(bbox.__class__ == region,
                          LazyFormat("bounding box of %s is not a region")%(self,))


        @abstract_method(optional=True)
        def left_steenrod_action_milnor(self,ak,mk):
            """
            Compute the left action a*m where ak, mk are the basis keys of monomials
            in the Milnor basis version of the Steenrod algebra, resp. the module.

            TESTS::

                sage: from yacop.modules.categories import YacopLeftModules
                sage: class testclass(CombinatorialFreeModule):
                ....:     def __init__(self):
                ....:          CombinatorialFreeModule.__init__(self,GF(2),ZZ,category=YacopLeftModules(SteenrodAlgebra(2)))
                ....:     def left_steenrod_action_milnor(self,ak,mk):
                ....:          print("left_steenrod_action_milnor(%s,%s)"%(ak,mk))
                ....:          return self.zero()
                sage: C = testclass()
                sage: Sq(3) * C.monomial(17)
                left_steenrod_action_milnor((3,),17)
                0
                sage: Sq(3) % C.monomial(17)
                left_steenrod_action_milnor((0, 1),17)
                left_steenrod_action_milnor((3,),17)
                0
            """

        @abstract_method(optional=True)
        def right_steenrod_action_milnor(self,mk,ak):
            """
            Compute the right action m*a where ak, mk are the basis keys of monomials
            in the Milnor basis version of the Steenrod algebra, resp. the module.

            TESTS::

                sage: from yacop.modules.categories import YacopRightModules
                sage: class testclass(CombinatorialFreeModule):
                ....:     def __init__(self):
                ....:          CombinatorialFreeModule.__init__(self,GF(2),ZZ,category=YacopRightModules(SteenrodAlgebra(2)))
                ....:     def right_steenrod_action_milnor(self,ak,mk):
                ....:          print("right_steenrod_action_milnor(%s,%s)"%(ak,mk))
                ....:          return self.zero()
                sage: C = testclass()
                sage: C.monomial(17) * Sq(3)
                right_steenrod_action_milnor(17,(3,))
                0
                sage: C.monomial(17) % Sq(3)
                right_steenrod_action_milnor(17,(0, 1))
                right_steenrod_action_milnor(17,(3,))
                0
            """

        @abstract_method(optional=True)
        def left_steenrod_action_milnor_conj(self,ak,mk):
            """
            Compute the conjugate action conj(a)*m where ak, mk are the basis keys of
            monomials in the Milnor basis version of the Steenrod algebra, resp. the module.

            TESTS::

                sage: from yacop.modules.categories import YacopLeftModules
                sage: class testclass(CombinatorialFreeModule):
                ....:     def __init__(self):
                ....:          CombinatorialFreeModule.__init__(self,GF(2),ZZ,category=YacopLeftModules(SteenrodAlgebra(2)))
                ....:     def left_steenrod_action_milnor_conj(self,ak,mk):
                ....:          print("left_steenrod_action_milnor_conj(%s,%s)"%(ak,mk))
                ....:          return self.zero()
                sage: C = testclass()
                sage: Sq(3) * C.monomial(17)
                left_steenrod_action_milnor_conj((0, 1),17)
                left_steenrod_action_milnor_conj((3,),17)
                0
                sage: Sq(3) % C.monomial(17)
                left_steenrod_action_milnor_conj((3,),17)
                0
            """

        @abstract_method(optional=True)
        def right_steenrod_action_milnor_conj(self,mk,ak):
            """
            Compute the conjugate action m*conj(a) where ak, mk are the basis keys of
            monomials in the Milnor basis version of the Steenrod algebra, resp. the module.

            TESTS::

                sage: from yacop.modules.categories import YacopRightModules
                sage: class testclass(CombinatorialFreeModule):
                ....:     def __init__(self):
                ....:          CombinatorialFreeModule.__init__(self,GF(2),ZZ,category=YacopRightModules(SteenrodAlgebra(2)))
                ....:     def right_steenrod_action_milnor_conj(self,ak,mk):
                ....:          print("right_steenrod_action_milnor_conj(%s,%s)"%(ak,mk))
                ....:          return self.zero()
                sage: C = testclass()
                sage: C.monomial(17) * Sq(3)
                right_steenrod_action_milnor_conj(17,(0, 1))
                right_steenrod_action_milnor_conj(17,(3,))
                0
                sage: C.monomial(17) % Sq(3)
                right_steenrod_action_milnor_conj(17,(3,))
                0
            """

        @lazy_attribute
        def left_steenrod_action_on_basis(self):
            """
            TESTS::

                sage: from yacop.modules.categories import YacopLeftModules
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

                sage: from yacop.modules.categories import YacopRightModules
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

        def _left_action_from_milnor_conj(self,a,m):
            return self._action_from_milnor(self.left_steenrod_action_milnor_conj,a.antipode(),m)

        def _right_action_from_milnor_conj(self,m,a):
            return self._action_from_milnor(self.right_steenrod_action_milnor_conj,m,a.antipode())

        def _left_conj_action_from_milnor(self,a,m):
            return self._action_from_milnor(self.left_steenrod_action_milnor,a.antipode(),m)

        def _right_conj_action_from_milnor(self,m,a):
            return self._action_from_milnor(self.right_steenrod_action_milnor,m,a.antipode())

        # direct implementations of actions and conjugate actions

        def _left_action_from_milnor(self,a,m):
            return self._action_from_milnor(self.left_steenrod_action_milnor,a.milnor(),m)

        def _right_action_from_milnor(self,m,a):
            return self._action_from_milnor(self.right_steenrod_action_milnor,m,a.milnor())

        def _left_conj_action_from_milnor_conj(self,a,m):
            return self._action_from_milnor(self.left_steenrod_action_milnor_conj,a.milnor(),m)

        def _right_conj_action_from_milnor_conj(self,m,a):
            return self._action_from_milnor(self.right_steenrod_action_milnor_conj,m,a.milnor())

        def _action_from_milnor(self,actfunc,a,m):
            adct = a.monomial_coefficients()
            mdct = m.monomial_coefficients()
            res = []
            for ak,cf1 in adct.iteritems():
                for mk,cf2 in mdct.iteritems():
                    d = actfunc(ak,mk)
                    res.append((d,cf1*cf2))
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

        def _manual_test_action(self, reg, opdeg=None, mode='left', verbose=False):
            """
            a check of the associativity of the steenrod algebra action
            """
            if mode == 'left':
                LHS = lambda op1,op2,a : (op1*op2)*a
                RHS = lambda op1,op2,a : op1*(op2*a)
            elif mode == 'right':
                LHS = lambda op1,op2,a : a*(op1*op2)
                RHS = lambda op1,op2,a : (a*op1)*op2
            elif mode == 'bimod':
                LHS = lambda op1,op2,a : (op1*a)*op2
                RHS = lambda op1,op2,a : op1*(a*op2)
            elif mode == 'leftconj':
                LHS = lambda op1,op2,a : (op1*op2)%a
                RHS = lambda op1,op2,a : op2%(op1%a)
            elif mode == 'rightconj':
                LHS = lambda op1,op2,a : a%(op1*op2)
                RHS = lambda op1,op2,a : (a%op2)%op1
            elif mode == 'bimodconj':
                LHS = lambda op1,op2,a : (op1%a)%op2
                RHS = lambda op1,op2,a : op1%(a%op2)
            else:
                raise ValueError, "unknown mode %s" % mode

            A = self._yacop_base_ring
            def abasis(i):
                for x in A[i].basis():
                    yield A(x)
            cnt = 0
            for b in self.graded_basis(reg):
                odeg = opdeg if not opdeg is None else reg.tmax - b.t 
                for i in range(0,odeg+1):
                    for op1 in abasis(i):
                        for j in range(0,odeg+1-i):
                            if verbose: print mode, b, i, j, cnt
                            for op2 in abasis(j):
                                val = LHS(op1,op2,b)
                                if val != RHS(op1,op2,b):
                                    print "ERROR (%s):" % mode
                                    print "op1",op1
                                    print "op2",op2
                                    print "  b",b
                                    print "LHS = ", LHS(op1,op2,b) 
                                    print "RHS = ", RHS(op1,op2,b)
                                    raise ValueError, "mismatch"
                                if not val.is_zero():
                                    cnt += 1
            print "%d non-zero multiplications checked" % cnt

        def differential(self,elem):
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

        def differential_set(self,lst):
            if self._differential_dict is None:
                self.differential_clear()
            for (elem,dst) in lst:
                if len(elem) != 1:
                    raise ValueError, "source element must be a monomial"
                (key,cf), = elem
                self._differential_dict[key] = (1/cf)*dst

        @lazy_attribute
        def _differential_morphism_from_dict(self):
            ans = self.module_morphism(codomain=self,on_basis=self._differential_from_dict)
            ans.rename("internal differential of %s" % self)
            return ans

        @lazy_attribute
        def _differential_morphism_from_basis(self):
            ans = self.module_morphism(codomain=self,on_basis=self._differential_on_basis)
            ans.rename("internal differential of %s" % self)
            return ans

        def _differential_on_basis(self,key):
            """
            default differential is zero
            """
            return self.zero()

        def _differential_from_dict(self,key):
            try:
                return self._differential_dict[key]
            except KeyError:
                return self.zero()

        def _Hom_(X,Y,category):
            # here we overwrite the Rings._Hom_ implementation
            return Homset(X, Y, category = category)

        def module_morphism(self,*args,**kwargs):
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
            cat = kwargs.pop('category',Y)
            codomain = kwargs.pop('codomain',self)
            cat = cat.category().meet((self.category(),codomain.category()))
            kwargs['category'] = cat
            kwargs['codomain'] = codomain
            ans = ModulesWithBasis(Y.base_ring().base_ring()).parent_class.module_morphism(self,*args,**kwargs)
            # there is a known issue with morphism categories (see sage code)
            # disable the _test_category and _test_pickling method for this instance:
            def dummy(*args,**kwopts):
               pass
            setattr(ans,"_test_category",dummy)
            setattr(ans,"_test_pickling",dummy)
            return ans

        # some routines (for example the combinatorial free modules' cartesian_product
        # cartesian_projection) use the underscored version instead
        _module_morphism = module_morphism

        def KernelOf(self,f,**options):
            """
            create the kernel of the map ``f``. ``domain(f)`` must be self.
            """
            from yacop.modules.morph_module import KernelImpl
            assert f.domain() is self
            return KernelImpl(f,**options)

        def ImageOf(self,f,**options):
            """
            create the image of the map ``f`` ``domain(f)`` must be self.
            """
            from yacop.modules.morph_module import ImageImpl
            assert f.codomain() is self
            return ImageImpl(f,**options)

        def CokernelOf(self,f,**options):
            """
            create the cokernel of the map ``f`` ``domain(f)`` must be self.
            """
            from yacop.modules.morph_module import CokerImpl
            assert f.codomain() is self
            return CokerImpl(f,**options)

        def _xx_test_truncation(self,tester = None,**options):
            from yacop.modules.functors import truncation
            from sage.misc.sage_unittest import TestSuite
            from sage.misc.lazy_format import LazyFormat
            is_sub_testsuite = (tester is not None)
            tester = self._tester(tester = tester, **options)
            myatt = "_truncation_tested"
            if not hasattr(self,myatt):
                # find a non-zero action a*m = n in self
                def testops(A):
                    for _ in A.some_elements():
                        yield _
                    maxdeg = A.prime()**3
                    for deg in range(1,maxdeg):
                        for key in A.homogeneous_component(maxdeg-deg+1).basis():
                            yield A(key)
                n = self.zero()
                for (deg,m) in self.an_element().homogeneous_decomposition().iteritems():
                    if not m.is_zero():
                        for a in testops(self._yacop_base_ring):
                            n = a*m
                            #print("trying %s*%s->%s"%(a,m,n))
                            if not n.is_zero():
                                break
                        if not n.is_zero():
                            break
                if n.is_zero() or m.t == n.t:
                    print("WARN: could not find a non-trivial action in %s" % self) 
                else:
                    tests = []
                    # tests are tuples: 
                    #   1 region to truncate to
                    #  flags whether
                    #   2 m survives to truncation
                    #   3 n survives to truncation
                    #  and
                    #   4 result of computing a*m in the truncation 
                    tests.append(((m.t,n.t),True,True,n))
                    tests.append(((m.t,m.t),True,False,0))
                    tests.append(((n.t,n.t),False,True,0))
                    for ((tmin,tmax),sm,sn,am) in tests:
                        T = truncation(self,tmin=tmin,tmax=tmax)
                        if sm:
                            tester.assertTrue(m in T,
                                    LazyFormat("contains (+) broken for %s (elem %s)")%(T,n))
                            tester.assertTrue(self(T(m))==m,
                                    LazyFormat("casting from/to truncation broken for %s (elem %s)")%(T,n))
                            tester.assertTrue(T(m).parent() is T,
                                    LazyFormat("wrong parent for %s (elem %s)")%(T,n))
                        else:
                            tester.assertTrue(not m in T,
                                    LazyFormat("contains (-) broken for %s (elem %s)")%(T,n))
                            ok = False;
                            try:
                                x = T(m)
                            except:
                                ok = True
                            tester.assertTrue(ok,
                                    LazyFormat("no exception when casting %s into %s" %(m,T)))
                        if sn:
                            tester.assertEqual(n,self(T(n)),
                                    LazyFormat("casting %s into %s destroys element" %(n,T)))
                        else:
                            tester.assertTrue(T(n).is_zero(),
                                    LazyFormat("%s does not map to zero in %s" %(n,T)))
                        if sm:
                            tester.assertEqual(a*T(m),T(am),
                                    LazyFormat("bad action %s * %s != %s" %(a,m,n)))
            # FIXME: run the TestSuite of a truncation (and avoid infinite loops)

        def _test_suspension(self,tester = None,**options):
            from sage.misc.sage_unittest import TestSuite
            from sage.misc.lazy_format import LazyFormat
            is_sub_testsuite = (tester is not None)
            tester = self._tester(tester = tester, **options)
            myatt = "_suspension_tested"
            if not hasattr(self,myatt):
                s = self.an_element()
                X = suspension(self,t=5,s=3)
                tester.assertTrue(X is suspension(self,t=5,s=3),
                        LazyFormat("suspension(X,..) is not suspension(X,..) for X=%s")%(X,))
                setattr(X,myatt,"yo")
                try:
                    tester.info("\n  Running the test suite of a suspension")
                    TestSuite(X).run(verbose = tester._verbose, prefix = tester._prefix+"  ",
                                            raise_on_failure = is_sub_testsuite)
                    tester.info(tester._prefix+" ", newline = False)
                    x = s.suspend(t=5,s=3)
                    x3 = s.suspend(t=5,s=3)
                    x2 = self.suspend_element(s,t=5,s=3)
                    tester.assertEqual(x,x3,
                                LazyFormat("x.suspend(...) != x.suspend(...):\n   A=%s\n   B=%s")%(x,x3,))
                    tester.assertEqual(x,x2,
                                LazyFormat("x.suspend(...) != parent.suspend_element(x,...):\n   A=%s\n   B=%s")%(x,x2,))
                    tester.assertTrue(x.parent()==X,
                                LazyFormat("suspended element %s not in suspension %s")%(x,X,))
                finally:
                    delattr(X,myatt)

        def _test_cartesian_product(self,tester = None,**options):
            from sage.misc.sage_unittest import TestSuite
            from sage.misc.lazy_format import LazyFormat
            if hasattr(self,"_suspension_tested"):
               return # avoids infinity test cycle
            is_sub_testsuite = (tester is not None)
            tester = self._tester(tester = tester, **options)
            myatt = "_ycp_cartesian_product_tested"
            if not hasattr(self,myatt):
              X = cartesian_product((self,self))
              setattr(X,myatt,"yo")
              try:
               tester.info("\n  Running the test suite of (self (+) self)")
               TestSuite(X).run(verbose = tester._verbose, prefix = tester._prefix+"  ",
                                      raise_on_failure = is_sub_testsuite)
               f = X.cartesian_projection(0)
               tester.info("\n  Running the test suite of the projection (self (+) self) -> self")
               TestSuite(f).run(verbose = tester._verbose, prefix = tester._prefix+"  ",
                                      raise_on_failure = is_sub_testsuite, skip = ["_test_category", "_test_nonzero_equal", "_test_pickling"])
               f = X.summand_embedding(1)
               tester.info("\n  Running the test suite of the embedding self -> (self (+) self)")
               TestSuite(f).run(verbose = tester._verbose, prefix = tester._prefix+"  ",
                                      raise_on_failure = is_sub_testsuite, skip = ["_test_category", "_test_nonzero_equal", "_test_pickling"])
              finally:
               delattr(X,myatt)

        def dump_element(self,el):
            """
            Create a string representation of the element.
            The default implementation uses 'dumps' and is very inefficient.

            .. note:: the string must be unambigously determined by the element.
            """
            import base64
            return base64.b64encode(dumps(el))

        def load_element(self,str):
            """
            Create element from its string representation.
            The default implementation uses 'loads' and is very inefficient.
            """
            import base64
            return loads(bse64.b64decode(str))

        def _test_dump_element(self,tester = None,**options):
            tester = self._tester(tester = tester, **options)
            from sage.misc.sage_unittest import TestSuite
            from sage.misc.lazy_format import LazyFormat
            for (cnt,el) in zip(range(0,10),self.some_elements()):
                str = self.dump_element(el)
                oth = self.load_element(str)
                tester.assertEqual(el,oth,
                                   LazyFormat("load_element(dump_element(el)) != el for el = %s")%el)

        def _can_test_pickling(self):
            """
            Some objects (e.g., morphisms, kernels of morphisms, ...) cannot be pickled.
            """
            return True

        def _check_adem_relations(self,region=None,act_left=True):
            pass

        def _check_action(self,region=None,act_left=True):
            pass

    class ElementMethods:

        @lazy_attribute
        def t(self):
            return self.degree().tmin

        @lazy_attribute
        def e(self):
            return self.degree().emin

        @lazy_attribute
        def s(self):
            return self.degree().smin

        def _can_test_pickling(self):
            return self.parent()._can_test_pickling()

        def differential(self):
            return self.parent().differential(self)

    class _TensorProducts(TensorProductsCategory):
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

            def left_steenrod_action_on_basis(self,a,elem):
                return self.linear_combination((self.monomial(tuple(k)),c)
                    for (k,c) in self.__act_left(a,self._sets,elem))

            def right_steenrod_action_on_basis(self,elem,a):
                return self.linear_combination((self.monomial(tuple(k)),c)
                    for (k,c) in self.__act_right(elem,self._sets,a))

            def left_conj_steenrod_action_on_basis(self,a,elem):
                return self.linear_combination((self.monomial(tuple(k)),c)
                    for (k,c) in self.__act_left_conj(a,self._sets,elem))

            def right_conj_steenrod_action_on_basis(self,elem,a):
                return self.linear_combination((self.monomial(tuple(k)),c)
                    for (k,c) in self.__act_right_conj(elem,self._sets,a))

            def __act_left(self,a,parents,elem):
                for (key,cf) in elem:
                    M0 = parents[0]
                    m0 = M0._from_dict({key[0]:cf})
                    if len(parents)==1:
                        for (k,c) in M0.left_steenrod_action_on_basis(a,m0):
                            yield [k,],c
                    else:
                        A = a.parent()
                        cop = a.coproduct()
                        for ((k1,k2),acf) in cop:
                            a1 = A._from_dict({k1:acf})
                            a2 = A.monomial(k2)
                            deg2 = a2.degree()
                            for (k1,c1) in M0.left_steenrod_action_on_basis(a1,m0):
                                for (k,c) in self.__act_left(a2,parents[1:],[(key[1:],c1),]):
                                    if (deg2&1) and (m0.e&1): c=-c
                                    yield [k1,]+k,c

            def __act_right(self,elem,parents,a):
                ln = len(parents)-1
                for (key,cf) in elem:
                    M0 = parents[ln]
                    m0 = M0._from_dict({key[ln]:cf})
                    if len(parents)==1:
                        for (k,c) in M0.right_steenrod_action_on_basis(m0,a):
                            yield [k,],c
                    else:
                        A = a.parent()
                        cop = a.coproduct()
                        for ((k1,k2),acf) in cop:
                            a1 = A._from_dict({k1:acf})
                            a2 = A.monomial(k2)
                            deg1 = a1.degree()
                            for (k1,c1) in M0.right_steenrod_action_on_basis(m0,a2):
                                for (k,c) in self.__act_right([(key[:ln],c1),],parents[:ln],a1):
                                    if (deg1&1) and (m0.e&1): c=-c
                                    yield k+[k1,],c

            def __act_left_conj(self,a,parents,elem):
                for (key,cf) in elem:
                    M0 = parents[0]
                    m0 = M0._from_dict({key[0]:cf})
                    if len(parents)==1:
                        for (k,c) in M0.left_conj_steenrod_action_on_basis(a,m0):
                            yield [k,],c
                    else:
                        A = a.parent()
                        cop = a.coproduct()
                        for ((k1,k2),acf) in cop:
                            a1 = A._from_dict({k1:acf})
                            a2 = A.monomial(k2)
                            deg2 = a2.degree()
                            for (k1,c1) in M0.left_conj_steenrod_action_on_basis(a1,m0):
                                for (k,c) in self.__act_left_conj(a2,parents[1:],[(key[1:],c1),]):
                                    if (deg2&1) and (m0.e&1): c=-c
                                    yield [k1,]+k,c

            def __act_right_conj(self,elem,parents,a):
                ln = len(parents)-1
                for (key,cf) in elem:
                    M0 = parents[ln]
                    m0 = M0._from_dict({key[ln]:cf})
                    if len(parents)==1:
                        for (k,c) in M0.right_conj_steenrod_action_on_basis(m0,a):
                            yield [k,],c
                    else:
                        A = a.parent()
                        cop = a.coproduct()
                        for ((k1,k2),acf) in cop:
                            a1 = A._from_dict({k1:acf})
                            a2 = A.monomial(k2)
                            deg1 = a1.degree()
                            for (k1,c1) in M0.right_conj_steenrod_action_on_basis(m0,a2):
                                for (k,c) in self.__act_right_conj([(key[:ln],c1),],parents[:ln],a1):
                                    if (deg1&1) and (m0.e&1): c=-c
                                    yield k+[k1,],c


            def _differential_on_basis(self,keys):
                """
                Internal differential of a tensor product of modules

                TESTS::

                    sage: fix me!
                """
                ans = []
                for (i,mod) in enumerate(self._sets):
                    a = keys[:i]
                    b = mod._differential_on_basis(keys[i])
                    c = keys[i+1:]
                    for (key,cf) in b:
                        if 0 != (i&1):
                            cf = -cf
                        ans.append((tuple(list(a)+[key,]+list(c)),cf))
                return self._from_dict(dict(ans))

            @staticmethod
            def SuspendedObjectsFactory(module,*args,**kwopts):
                from sage.categories.tensor import tensor
                l = len(module._sets)
                last = module._sets[l-1]
                newsets = list(module._sets[:l-1]) + [suspension(last,*args,**kwopts),]
                return tensor(tuple(newsets))

        class ElementMethods:
            def _can_test_pickling(self):
                return self.parent()._can_test_pickling()

    class _CartesianProducts(CartesianProductsCategory):
        """
        direct sums of modules.
        """

        def extra_super_categories(self):
            return []

        def super_categories(self):
            """
            Sage thinks the cartesian product of algebras is an algebra, but we disagree:

            TESTS::

                sage: from yacop.modules.categories import *
                sage: D=YacopLeftModuleAlgebras(SteenrodAlgebra(3)).CartesianProducts() ; D
                Category of Cartesian products of left Yacop module algebras over mod 3 Steenrod algebra, milnor basis
                sage: D.super_categories()
                [Category of left Yacop modules over mod 3 Steenrod algebra, milnor basis,
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
            if self.base_category()._is_algebra:
                obj = self.base_category().ModuleCategory().CartesianProducts()
            return [self.base_category().ModuleCategory(),] + super(SteenrodAlgebraModules._CartesianProducts,obj).super_categories()

        def Subquotients(self):
             """
             A subobject or quotient of a direct sum is no longer a direct sum
             """
             return self.base_category().Subquotients()

        class ElementMethods:
            def _can_test_pickling(self):
               return self.parent()._can_test_pickling()

        class ParentMethods:

            def left_steenrod_action_on_basis(self,a,m):
                smds = []
                for i in range(0,len(self._sets)):
                    Mi = self._sets[i]
                    mi = self.cartesian_projection(i)(m)
                    ami = Mi.left_steenrod_action_on_basis(a,mi)
                    smds.append(self.summand_embedding(i)(ami))
                return self.sum(smds)

            def right_steenrod_action_on_basis(self,m,a):
                smds = []
                for i in range(0,len(self._sets)):
                    Mi = self._sets[i]
                    mi = self.cartesian_projection(i)(m)
                    ami = Mi.right_steenrod_action_on_basis(mi,a)
                    smds.append(self.summand_embedding(i)(ami))
                return self.sum(smds)

            def left_conj_steenrod_action_on_basis(self,a,m):
                smds = []
                for i in range(0,len(self._sets)):
                    Mi = self._sets[i]
                    mi = self.cartesian_projection(i)(m)
                    ami = Mi.left_conj_steenrod_action_on_basis(a,mi)
                    smds.append(self.summand_embedding(i)(ami))
                return self.sum(smds)

            def right_conj_steenrod_action_on_basis(self,m,a):
                smds = []
                for i in range(0,len(self._sets)):
                    Mi = self._sets[i]
                    mi = self.cartesian_projection(i)(m)
                    ami = Mi.right_conj_steenrod_action_on_basis(mi,a)
                    smds.append(self.summand_embedding(i)(ami))
                return self.sum(smds)

            def _differential_on_basis(self,key):
                idx,k = key
                mod = self._sets[idx]
                return self.summand_embedding(idx)(mod.differential(mod.monomial(k)))

            def _repr_term(self,elem):
                return "(%s)" % ", ".join(mod._repr_term(mod.cartesian_projection(i)(elem)) for (mod,i) in zip(self._sets,self._set_keys))

            def suspend_element(self,m,**options):
                susp = suspension(self,**options)
                smds = []
                for i in range(0,len(self._sets)):
                    Mi = self._sets[i]
                    mi = self.cartesian_projection(i)(m)
                    mis = Mi.suspend_element(mi,**options)
                    # hack: we might have nonidentical parents here: mis.parent() != susp._sets[i]
                    mis._set_parent(susp._sets[i])
                    smds.append(susp.summand_embedding(i)(mis))
                return susp.sum(smds)


            @staticmethod
            def SuspendedObjectsFactory(module,*args,**kwopts):
                from sage.categories.cartesian_product import cartesian_product
                return cartesian_product([suspension(mod,*args,**kwopts) for mod in module._sets])

            def _can_test_pickling(self):
                return all(m._can_test_pickling() for m in self._sets)


    class _DualObjects(DualObjectsCategory):

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

    class _SuspendedObjects(SuspendedObjectsCategory):

        """
        TESTS::

            sage: import yacop.modules
            sage: C=yacop.modules.categories.YacopLeftModuleAlgebras(SteenrodAlgebra(3))
            sage: C.SuspendedObjects()
            Category of suspensions of left Yacop module algebras over mod 3 Steenrod algebra, milnor basis

        """

        @cached_method
        def extra_super_categories(self):
           return [self.base_category().ModuleCategory()]

        def base_ring(self):
           return self.base_category().base_ring()

        class ParentMethods:
           pass

    class _TruncatedObjects(TruncatedObjectsCategory):

        """
        TESTS::

            sage: import yacop.modules
            sage: C=yacop.modules.categories.YacopLeftModuleAlgebras(SteenrodAlgebra(3))
            sage: C.TruncatedObjects()
            Category of truncations of left Yacop module algebras over mod 3 Steenrod algebra, milnor basis

        """

        @cached_method
        def extra_super_categories(self):
            return [self.base_category().ModuleCategory()]

        def base_ring(self):
           return self.base_category().base_ring()

        class ParentMethods:
            pass

    class _Homsets(HomsetsCategory):
        """
        TESTS::

            sage: from yacop.modules.categories import *
            sage: C = YacopLeftModules(SteenrodAlgebra(3))
            sage: C.Homsets()
            Category of homsets of left Yacop modules over mod 3 Steenrod algebra, milnor basis
        """

        def _repr_object_names(self):
            return "homsets of %s" % self.base_category()._repr_object_names()

        def extra_super_categories(self):
            # TODO: make this a Steenrod algebra module
            return [ModulesWithBasis(self.base_category().ModuleCategory().base_ring()).Homsets(),]

        def super_categories(self):
            # TODO: make this a Steenrod algebra module
            return [ModulesWithBasis(self.base_category().ModuleCategory().base_ring()).Homsets(),]

        class ParentMethods:
            pass

        class ElementMethods:

            def _test_nonzero_equal(self, **options):
                pass

            def kernel(self):
               M = self.domain()
               if hasattr(M,"KernelOf"):
                  return M.KernelOf(self)
               raise NotImplementedError, "kernel of map from %s not implemented" % M

            def image(self):
               N = self.codomain()
               if hasattr(N,"ImageOf"):
                  return N.ImageOf(self)
               raise NotImplementedError, "image of map into %s not implemented" % N

            def cokernel(self):
               N = self.codomain()
               if hasattr(N,"CokernelOf"):
                  return N.CokernelOf(self)
               raise NotImplementedError, "cokernel of map into %s not implemented" % N

            @staticmethod
            def SuspendedObjectsFactory(self,*args,**kwopts):
               """
               suspension of morphisms.

               TESTS::

                  sage: from yacop.modules.functors import suspension
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
               M,N = self.domain(), self.codomain()
               SM,SN = [suspension(x,**kwopts) for x in (M,N)]
               lam = lambda i: self(M.monomial(i)).suspend(**kwopts)
               res = SM.module_morphism(codomain=SN,on_basis = lam)
               res.rename("suspension of %s"%self)
               return res

            def _test_suspension(self,tester=None):
               pass

    class _Subquotients(SubquotientsCategory):
     """
     A subquotient of a Steenrod algebra module or algebra

     TESTS::

          sage: from yacop.modules.categories import *
          sage: C = YacopLeftModuleAlgebras(SteenrodAlgebra(11))
          sage: D = YacopLeftModules(SteenrodAlgebra(11))
          sage: C.Subquotients()
          Category of subquotients of left Yacop module algebras over mod 11 Steenrod algebra, milnor basis
          sage: D.Subquotients()
          Category of subquotients of left Yacop modules over mod 11 Steenrod algebra, milnor basis
     """

     def _repr_object_names(self):
         return "subquotients of %s" % self.base_category()._repr_object_names()

     @cached_method
     def super_categories(self):
      """
      A subquotient should again be a Steenrod algebra module, but not an algebra.

      TESTS::

         sage: from yacop.modules.categories import *
         sage: C = YacopLeftModules(SteenrodAlgebra(3))
         sage: D = C.Subquotients() ; D
         Category of subquotients of left Yacop modules over mod 3 Steenrod algebra, milnor basis
         sage: C in D.all_super_categories()
         True
         sage: E = YacopLeftModuleAlgebras(SteenrodAlgebra(3))
         sage: F = E.Subquotients() ; F
         Category of subquotients of left Yacop module algebras over mod 3 Steenrod algebra, milnor basis
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

      def left_steenrod_action_on_basis(self,a,m):
         amb = self.ambient()
         return self.retract(amb.left_steenrod_action_on_basis(a,self.lift(m)))

      def right_steenrod_action_on_basis(self,m,a):
         amb = self.ambient()
         return self.retract(amb.right_steenrod_action_on_basis(self.lift(m),a))

      def left_conj_steenrod_action_on_basis(self,a,m):
         amb = self.ambient()
         return self.retract(amb.left_conj_steenrod_action_on_basis(a,self.lift(m)))

      def right_conj_steenrod_action_on_basis(self,m,a):
         amb = self.ambient()
         return self.retract(amb.right_conj_steenrod_action_on_basis(self.lift(m),a))

      def lift(self,elem):
         """
         Lift an element of ``self`` to ``self.ambient()`` as per ``Subquotients`` category.

         This default implementation delegates its work to self._lift_homogeneous.
         """
         ans=[]
         for (deg,smd) in elem.homogeneous_decomposition().iteritems():
            ans.append(self._lift_homogeneous(deg,smd))
         return self.parent().ambient().sum(ans)

      def retract(self,elem):
         """
         Retract an element of ``self.ambient()`` to ``self`` as per ``Subquotients`` category.

         This default implementation delegates its work to self._retract_homogeneous.
         """
         ans=[]
         for (deg,smd) in elem.homogeneous_decomposition().iteritems():
            ans.append(self._retract_homogeneous(deg,smd))
         return self.parent().sum(ans)

    # thanks to a recently introduced Sage hack we have to provide a few dummy assignments
    CartesianProducts = 1
    SuspendedObjects  = 1
    TensorProducts = 1
    DualObjects = 1
    TruncatedObjects = 1
    Subquotients = 1
    Homsets = 1

def SubquotientsImpl(self):
   if self._is_algebra:
      return self.ModuleCategory().Subquotients()
   return SteenrodAlgebraModules._Subquotients(self)

#SteenrodAlgebraModules._Subquotients = SubquotientsImpl

class YacopLeftModules(SteenrodAlgebraModules):
    def __init__(self,R):
        super(YacopLeftModules,self).__init__(R,is_left=True,is_right=False,is_bimod=False,is_algebra=False)

class YacopRightModules(SteenrodAlgebraModules):
    def __init__(self,R):
        super(YacopRightModules,self).__init__(R,is_left=False,is_right=True,is_bimod=False,is_algebra=False)

class YacopBiModules(SteenrodAlgebraModules):
    def __init__(self,R):
        super(YacopBiModules,self).__init__(R,is_left=True,is_right=True,is_bimod=True,is_algebra=False)

class YacopLeftModuleAlgebras(SteenrodAlgebraModules):
    def __init__(self,R):
        super(YacopLeftModuleAlgebras,self).__init__(R,is_left=True,is_right=False,is_bimod=False,is_algebra=True)

class YacopRightModuleAlgebras(SteenrodAlgebraModules):
    def __init__(self,R):
        super(YacopRightModuleAlgebras,self).__init__(R,is_left=True,is_right=True,is_bimod=False,is_algebra=True)

class YacopBiModuleAlgebras(SteenrodAlgebraModules):
    def __init__(self,R):
        super(YacopBiModuleAlgebras,self).__init__(R,is_left=True,is_right=True,is_bimod=True,is_algebra=True)

"""
   HACK: the __classget__ method of CovariantConstructionCategory tries to look behind the
   functor category (eg. CartesianProducts) and retrieve a hidden method of the same
   name underneath (from class Category). This fails if there is another such class in the
   class hierarchy. For this reason we cannot have "SteenrodAlgebraModules.CartesianProducts"
   between "Category.CartesianProducts" and "YacopRightModuleAlgebras.CartesianProducts".
"""

def make_functor_class(cls,fname,tmpl):
    from types import MethodType
    ncls=type("%s_%s"%(cls.__name__,fname),  (tmpl,), {})
    globals()[ncls.__name__] = ncls # required for pickling
    return MethodType(ncls,None,cls)

for cls in (YacopLeftModules, YacopRightModules, YacopBiModules,
            YacopLeftModuleAlgebras, YacopRightModuleAlgebras, YacopBiModuleAlgebras):
    cls.CartesianProducts = make_functor_class(cls,"CartesianProducts",SteenrodAlgebraModules._CartesianProducts)
    cls.SuspendedObjects  = make_functor_class(cls,"SuspendedObjects",SteenrodAlgebraModules._SuspendedObjects)
    cls.TensorProducts = make_functor_class(cls,"TensorProducts",SteenrodAlgebraModules._TensorProducts)
    cls.DualObjects = make_functor_class(cls,"DualObjects",SteenrodAlgebraModules._DualObjects)
    cls.TruncatedObjects = make_functor_class(cls,"TruncatedObjects",SteenrodAlgebraModules._TruncatedObjects)
    cls.Subquotients = make_functor_class(cls,"Subquotients",SteenrodAlgebraModules._Subquotients)
    cls.Homsets = make_functor_class(cls,"Homsets",SteenrodAlgebraModules._Homsets)

"""
  TESTS::

      sage: import __main__
      sage: from yacop.modules.categories import *
      sage: __main__.SteenrodAlgebraModules = SteenrodAlgebraModules
      sage: __main__.YacopLeftModules = YacopLeftModules
      sage: __main__.YacopRightModules = YacopRightModules
      sage: __main__.YacopBiModules = YacopBiModules
      sage: __main__.YacopLeftModuleAlgebras = YacopLeftModuleAlgebras
      sage: __main__.YacopRightModuleAlgebras = YacopRightModuleAlgebras
      sage: __main__.YacopBiModuleAlgebras = YacopBiModuleAlgebras
      sage: TestSuite(YacopLeftModules(SteenrodAlgebra(3))).run()
      sage: TestSuite(YacopRightModules(SteenrodAlgebra(3))).run()
      sage: TestSuite(YacopBiModules(SteenrodAlgebra(3))).run()
      sage: TestSuite(YacopLeftModuleAlgebras(SteenrodAlgebra(3))).run()
      sage: TestSuite(YacopRightModuleAlgebras(SteenrodAlgebra(3))).run()
      sage: TestSuite(YacopBiModuleAlgebras(SteenrodAlgebra(3))).run()
"""

"""
Test Category.meet: this should automatically restrict the Steenrod algebra action to a common subalgebra.

TESTS::

    sage: from yacop.modules.categories import *
    sage: A = SteenrodAlgebra(3)
    sage: B = SteenrodAlgebra(3,profile=((1,),(2,2)))
    sage: C = SteenrodAlgebra(3,profile=((),(1,2)))
    sage: D = SteenrodAlgebra(2)
    sage: YA, YB, YC, YD = [YacopLeftModules(X) for X in (A,B,C,D)]
    sage: Category.meet((YA,YB)) is YB
    True
    sage: Category.meet((YB,YC)) is YC
    True
    sage: Category.meet((YA,YB,YC)) is YC
    True
    sage: Category.meet((YA,YD))
    Join of Category of commutative additive groups and Category of yacop graded objects
    sage: YacopLeftModuleAlgebras(A)._meet_(YacopLeftModuleAlgebras(B)) is YacopLeftModuleAlgebras(B)
    True
    sage: YacopLeftModuleAlgebras(A)._meet_(YacopLeftModules(B)) is YacopLeftModules(B)
    True
    sage: YacopLeftModules(A)._meet_(YacopLeftModuleAlgebras(B)) is YacopLeftModules(B)
    True
    sage: YacopBiModules(B)._meet_(YacopRightModuleAlgebras(B)) is YacopRightModules(B)
    True
    
"""

def steenrod_algebra_intersect(algebras):
    """
    TESTS::
    
         sage: from yacop.modules.categories import *
         sage: A = SteenrodAlgebra(3)
         sage: B = SteenrodAlgebra(3,profile=((1,),(2,2)))
         sage: C = SteenrodAlgebra(3,profile=((),(1,2)))
         sage: steenrod_algebra_intersect((A,B))
         sub-Hopf algebra of mod 3 Steenrod algebra, milnor basis, profile function ([1], [2, 2])
    """
    from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra
    for dummy in (0,):
        A0 = algebras[0]
        if not all(A.prime() == A0.prime() for A in algebras): 
            break
        if not all(A.is_generic() == A0.is_generic() for A in algebras): 
            break
        rtrunc = +Infinity if all(A._truncation_type>0 for A in algebras) else 0
        isgen = A0.is_generic()
        profiles = [A._profile for A in algebras] if isgen else [(A._profile,()) for A in algebras] 
        proflen = max([0,] + [len(p[0]) for p in profiles] + [len(p[1]) for p in profiles])
        nprof0 = [min(A.profile(i,component=0) for A in algebras) for i in range(1,proflen+1)]
        nprof1 = [min(A.profile(i,component=1) for A in algebras) for i in range(0,proflen)]
        prof = (nprof0,nprof1) if isgen else nprof0
        #return prof
        res = SteenrodAlgebra(A.prime(),generic=isgen,profile=prof,truncation_type=rtrunc)
        return res
    raise ValueError, "algebras not compatible"


# fix module_morphism doc string
C = ModulesWithBasis(GF(2)).parent_class
SteenrodAlgebraModules.ParentMethods.module_morphism.__func__.__doc__ = C.module_morphism.__doc__

# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

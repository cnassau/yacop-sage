r"""
The Yacop base category for graded objects

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
from yacop.categories.functors import SuspendedObjectsCategory
from yacop.categories.functors import TruncatedObjectsCategory
from sage.misc.cachefunc import cached_function
from sage.misc.classcall_metaclass import typecall, ClasscallMetaclass
from yacop.categories.functors import suspension
from sage.misc.lazy_attribute import lazy_attribute
from sage.rings.all import GF
from sage.categories.homset import Homset
from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra

from yacop.categories.utils import is_yacop_category

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
       return "yacop objects"

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

        def yacop_categories(self):
            return [C for C in self.categories() if is_yacop_category(C)]

    class SubcategoryMethods:

        def CartesianProducts(self):
            return CartesianProductsCategory.category_of(self)

        def Subquotients(self):
            return SubquotientsCategory.category_of(self)

        def TensorProducts(self):
            return TensorProductsCategory.category_of(self)

        def SuspendedObjects(self):
            return SuspendedObjectsCategory.category_of(self)

class YacopGradedObjects(Category_singleton):
    """
    Category of pairs (M,G) where G is a Grading

    EXAMPLES::

        sage: from yacop.categories import *
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

            sage: from yacop.categories import *
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

                sage: from yacop.categories import *
                sage: YacopGradedObjects().example().grading()
                mod 7 decomposition of the range {1, ..., 18}

            """
            return self._yacop_grading

        @abstract_method(optional=True) # why allow optional
        def _yacop_clone(self,new_grading):
            """
            Factory function that returns a clone of self with a changed grading.

            This function is used by truncations and suspensions to implement
            operations on the grading (unless the object implements its own factory
            for those functors).
            """
            raise NotImplementedError

        def _some_homogeneous_elements(self):
            el = self.an_element()
            if hasattr(el,"homogeneous_decomposition"):
                sp = el.homogeneous_decomposition()
                return list(sp.items())
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
                for (deg,elem) in list(sp.items()):
                    b = self.grading().basis(deg)
                    c = self.graded_basis_coefficients(elem,deg)
                    sm = sum(cf*be for (cf,be) in zip(c,b))
                    if elem != sm:
                        print(("self=",self))
                        print(("elem=",elem))
                        print(("deg=",deg))
                        print(("graded basis=",list(b)))
                        print(("lhs=",elem.monomial_coefficients()))
                        print(("rhs=",sm.monomial_coefficients()))
                    tester.assertEqual(elem,sm,
                                       LazyFormat("graded_basis_coefficients failed on element %s of %s: sums to %s")
                                       %(elem,self,sm))

                el2 = sum(smd for (key,smd) in list(sp.items()))
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

            sage: from yacop.categories import *
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

        @lazy_attribute
        def t(self):
            return self.degree().tmin

        @lazy_attribute
        def e(self):
            return self.degree().emin

        @lazy_attribute
        def s(self):
            return self.degree().smin

    class SubcategoryMethods:
        pass

    class Subquotients(SubquotientsCategory):
        """
        TESTS::

            sage: from yacop.categories import *
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

            sage: from yacop.categories import *
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

            sage: from yacop.categories import *
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

# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

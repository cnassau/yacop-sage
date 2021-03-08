r"""
A base class for Steenrod algebra modules.

AUTHORS: - Christian Nassau (2011-05-13: version 1.0)

CLASS DOCUMENTATION:
"""

#*****************************************************************************
#       Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#  Distributed under the terms of the GNU General Public License (GPL)
#*****************************************************************************

from yacop.utils.region import region
from yacop.utils.gradings import YacopGrading
from yacop.utils.bitstuff import N0
from yacop.utils.set_of_elements import SetOfMonomials
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
from sage.categories.all import AlgebrasWithBasis, EnumeratedSets, FiniteEnumeratedSets
from sage.sets.integer_range import IntegerRange
from sage.algebras.all import SteenrodAlgebra, Sq
from sage.rings.integer import Integer
from sage.structure.formal_sum import FormalSum, FormalSums
from sage.structure.unique_representation import UniqueRepresentation
from sage.misc.cachefunc import cached_method
from sage.arith.all import binomial
from sage.misc.lazy_format import LazyFormat
from sage.categories.category_types import Category_over_base

class SteenrodModuleGrading(YacopGrading):
    """
    Grading of a free module with a graded set as basis.
    """

    def __init__(self,basis,module):
        YacopGrading.__init__(self)
        self._basis = basis
        self._module = module

    def split_element(self,elem):
        mono = self._module.monomial
        dct = dict()
        for (key,cf) in elem.monomial_coefficients().items():
            dg = self._basis.degree(key)
            if dg in dct:
                dct[dg].append((mono(key),cf))
            else:
                dct[dg] = [(mono(key),cf)]
        for dg in dct:
            dct[dg] = self._module.linear_combination(dct[dg])
        return dct

    def bbox(self):
        return self._basis.bbox()

    def basis(self,reg=None):
        reg = region.intersect(self.bbox(),reg)
        bas = self._basis.truncate(reg)
        if bas.is_finite():
            card = -1
        else:
            card = Infinity
        return SetOfMonomials(self._module,bas,card)

def detect_prime(category):
    p = None
    for supcat in category.all_super_categories():
        try:
            if isinstance(supcat,Category_over_base):
                p = supcat.base_ring().characteristic()
                break
        except AttributeError:
            pass
    assert p is not None
    return p

class SteenrodModuleBase(CombinatorialFreeModule):

    def __init__(self,basis,grading=None,category=None):
        self._prime = detect_prime(category)
        CombinatorialFreeModule.__init__(self, GF(self._prime), basis,
                             category=category)

        if grading is None:
           grading = SteenrodModuleGrading(basis,self)
        self._set_grading(grading)
        self._fix_basis_tests()

    def _fix_basis_tests(self):
        # fix test failures of self.basis():
        # per default a LazyFamily cannot check membership
        import types
        b = self.basis()
        def contains(basis,x):
           try:
              k, = x.monomial_coefficients()
              return self.monomial(k) == x
           except:
              return False
        b._contains_ = types.MethodType(contains,b)
        def _test_pickling(self,tester=None,**options):
           # tired of printing warnings about pickling
           pass
        b._test_pickling = types.MethodType(_test_pickling,b)

    def parent(self):
        """
        Returns self::

           sage: from yacop.modules.projective_spaces import RealProjectiveSpace
           sage: M=RealProjectiveSpace()
           sage: M.parent() is M
           True

        This is a dummy method to make multiplication by Suspenders work::

           sage: from yacop.utils.suspenders import Suspender
           sage: from yacop.categories.functors import suspension
           sage: from yacop.modules.projective_spaces import RealProjectiveSpace
           sage: S=Suspender(t=4) ; M=RealProjectiveSpace()
           sage: S*M is suspension(M,t=4)
           True
           sage: S*M is M*S
           True

        Without the ``M.parent`` method this fails because we implicitly treat
        ``M`` as an Element.
        """
        return self

    def _mul_(self,other,switch_sides=False):
        if other in self.grading().suspenders():
            return other._act_on_(self,not switch_sides)
        return super(SteenrodModuleBase,self)._mul_(other,switch_sides=switch_sides)

    def _element_constructor_(self,elem):
      if hasattr(elem,"monomial_coefficients"):
         dct = elem.monomial_coefficients()
         try:
             if all(u in self.indices() for u in dct):
                 return self._from_dict(dct)
         except:
             pass
      return super(SteenrodModuleBase,self)._element_constructor_(elem)

    def dimension(self,region=None,**kwargs):
         """
         Return the vector space dimension of this module in the given region.
         """
         try:
            return len(self.graded_basis(region,**kwargs))
         except:
            return +Infinity

    def _test_basis_sanity(self,tester = None,**options):
       from sage.misc.sage_unittest import TestSuite
       is_sub_testsuite = (tester is not None)
       tester = self._tester(tester = tester, **options)
       tester.info("\n  Running the test suite of the basis family")
       self.basis().max_test_enumerated_set_loop = 10
       TestSuite(self.basis()).run(verbose = tester._verbose, prefix = tester._prefix+"  ",
                        raise_on_failure = is_sub_testsuite)
       tester.info(tester._prefix+" ", newline = False)
       tester.info("\n  Running the test suite of the basis keys")
       #list(self.basis().keys()).max_test_enumerated_set_loop = 10
       #TestSuite(list(self.basis().keys())).run(verbose = tester._verbose, prefix = tester._prefix+"  ",
       #                 raise_on_failure = is_sub_testsuite)
       tester.info(tester._prefix+" ", newline = False)

    @cached_method
    def some_elements(self,num=10):
        ans=[]
        from itertools import islice
        gens=list(islice(self.indices(),num+3))
        cfs=(2,3,5)
        for i in range(0,num):
            elm = self.linear_combination((self.monomial(g),c) for (g,c) in zip(gens[i:],cfs))
            cfs = tuple((u+7 for u in cfs))
            ans.append(elm)
        return ans

    @cached_method
    def an_element(self):
        return self.some_elements(1)[0]

    def _dump_term(self,el):
        return el

    def _load_term(self,el):
        return el

    def dump_element(self,el):
        dct = dict(el)
        return "%s" % [(self._dump_term(k),dct[k]) for k in sorted(dct) if dct[k] != 0]

    def load_element(self,str):
        lst =eval(str)
        return self._from_dict({self._load_term(t):k for (t,k) in lst})

    class Element(CombinatorialFreeModule.Element):

       def _repr_(self):
          old = super(SteenrodModuleBase.Element,self)._repr_()
          return self.parent().grading()._format_term(old)

       def _latex_(self):
          old = super(SteenrodModuleBase.Element,self)._latex_()
          return self.parent().grading()._latex_term(old)

       def _test_element_dumping(self,tester=None,**options):
          tester = self._tester(tester = tester, **options)
          par = self.parent()
          tester.assertTrue( par.load_element(par.dump_element(self)) == self,
                     LazyFormat("loading dump of %s does not give back original")
                        % (self,))

       def _test_element_grading(self,tester=None,**options):
          tester = self._tester(tester = tester, **options)
          par = self.parent()
          for (deg,elem) in self.homogeneous_decomposition().items():
              tester.assertTrue( not elem == par.zero(),
                     LazyFormat("zeroes in homogeneous_decomposition of %s") % (self,))
              try:
                  t,e,s = elem.t,elem.e,elem.s
              except:
                  tester.assertTrue( False, LazyFormat("element %s of %s does not have t,e,s attributes") % (self,par))
              reg = region(t=t,e=e,s=s)
              gb = par.graded_basis(reg)
              tester.assertTrue( len(gb)>0,
                     LazyFormat("graded basis of %s in %s empty, should contain %s")
                        % (par,reg,elem))
              gbm = set.union(*[set(x.monomials()) for x in gb])
              for m in elem.monomials():
                  tester.assertTrue(m in gbm,
                          LazyFormat("element %s of degree (%d,%d,%d) not in graded_basis of its degree")
                                            %(m,t,e,s))
              for (toff,eoff,soff) in [(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)]:
                  rg = region(t=t+toff,e=e+eoff,s=s+soff)
                  gb = par.graded_basis(rg)
                  if len(gb)>0:
                    gbm = set.union(*[set(x.monomials()) for x in gb])
                    for m in elem.monomials():
                       tester.assertTrue(not m in gbm,
                          LazyFormat("element %s of degree (%d,%d,%d) is also in graded_basis(%s)")
                                            %(m,t,e,s,rg))

def withbrackets(str,islatex):
    if str.find("+")<0 and str.find("-")<0:
        return str
    if islatex:
        return "\\left(%s\\right)" % str
    return "(%s)" % str

class SteenrodModuleBase_Tensor(CombinatorialFreeModule.Tensor,SteenrodModuleBase):

    @staticmethod
    def __classcall_private__(cls, modules, **options):
        modules = sum([module._sets if isinstance(module, SteenrodModuleBase_Tensor)
            else (module,) for module in modules], ())
        return super(SteenrodModuleBase_Tensor,cls).__classcall__(cls,modules,**options)

    def __init__(self,modules,**options):
        CombinatorialFreeModule.Tensor.__init__(self,modules,**options)
        # with sage 5.7.beta4 the basis has the wrong category
        if False:
            try:
                from sage.sets.family import Family
                cc = list(self.basis().keys()).cc # the CartesianProduct
                self._indices = Family(cc,lambda u:tuple(u))
                def contains(self,x):
                    return x in cc
                import types
                self._indices._contains_ = types.MethodType(contains,self.indices())
                self.basis.clear_cache()
            except AttributeError:
                pass
        self._fix_basis_tests()

    def _repr_term(self,term):
          # hack because our elements have a custom _repr_ and
          # which is bypassed by tensor._repr_term
          from sage.categories.tensor import tensor
          if hasattr(self, "_print_options"):
              symb = self._print_options['tensor_symbol']
          if symb is None:
              symb = tensor.symbol
          else:
              symb = tensor.symbol
          return symb.join(withbrackets(module.monomial(t)._repr_(),False) for (module, t) in zip(self._sets, term))

    def _latex_term(self,term):
        from sage.misc.latex import latex
        # hack because our elements have a custom _repr_ and
        # which is bypassed by tensor._repr_term
        symb = " \\otimes "
        return symb.join(withbrackets(latex(module.monomial(t)),True) for (module, t) in zip(self._sets, term))

    def _dump_term(self,el):
        return tuple(M._dump_term(x) for (M,x) in zip(self._sets,el))

    def _load_term(self,el):
        return tuple(M._load_term(x) for (M,x) in zip(self._sets,el))

    class Element(SteenrodModuleBase.Element,CombinatorialFreeModule.Tensor.Element):
        def _repr_(self):
            return super(SteenrodModuleBase.Element,self)._repr_()
        def _latex_(self):
            return super(SteenrodModuleBase.Element,self)._latex_()
        def _test_pickling(self,tester=None,**options):
            if self.parent()._can_test_pickling():
                super(SteenrodModuleBase_Tensor.Element,self)._test_pickling(tester=tester,**options)

SteenrodModuleBase.Tensor = SteenrodModuleBase_Tensor

class SteenrodModuleBase_CartesianProduct(CombinatorialFreeModule.CartesianProduct,SteenrodModuleBase):

    def __init__(self,modules,*args,**kwargs):
       CombinatorialFreeModule.CartesianProduct.__init__(self,modules,*args,**kwargs)
       self._fix_basis_tests()

    def _repr_term(self,elem):
       return "(%s)" % ", ".join(mod.monomial(u)._repr_() for (mod,u) in zip(self._sets,elem))

    def _latex_term(self,elem):
       return "(%s)" % ", ".join(mod.monomial(u)._latex_() for (mod,u) in zip(self._sets,elem))

    def cartesian_projection(self,idx):
       res = super(SteenrodModuleBase.CartesianProduct,self).cartesian_projection(idx)
       res.rename("cartesian_projection(%d) of %s" % (idx,self))
       return res

    def dump_element(self,el):
        return str([p.dump_element(self.cartesian_projection(n)(el)) for (n,p) in enumerate(self._sets)])

    def load_element(self,str):
        ps = [p.load_element(s) for (p,s) in zip(self._sets,eval(str))]
        return self.sum(self.summand_embedding(n)(e) for (n,e) in enumerate(ps))

    class Element(CombinatorialFreeModule.CartesianProduct.Element):
        def _repr_(self):
            p = self.parent()
            x = [p.cartesian_projection(j)(self) for j in range(0,len(p._sets))]
            return "(%s)" % (", ".join(s._repr_() for s in x))

        def _test_pickling(self,tester=None,**options):
            if self.parent()._can_test_pickling():
                super(SteenrodModuleBase_CartesianProduct.Element,self)._test_pickling(tester=tester,**options)

SteenrodModuleBase.CartesianProduct = SteenrodModuleBase_CartesianProduct

# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

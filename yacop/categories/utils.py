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
    raise ValueError("algebras not compatible")

# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

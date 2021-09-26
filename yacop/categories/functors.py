r"""
Operations on Steenrod algebra modules



AUTHORS:

 - Christian Nassau (2011): initial revision

"""
#*****************************************************************************
#  Copyright (C) 2011      Christian Nassau <nassau@nullhomotopie.de>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************

from sage.misc.abstract_method import abstract_method
from sage.misc.cachefunc import cached_method
from sage.misc.lazy_attribute import lazy_attribute
from sage.categories.category_types import Category_over_base_ring
from sage.categories.all import Category, Hom, Rings, Modules, LeftModules, RightModules, Bimodules, ModulesWithBasis, AlgebrasWithBasis
from sage.categories.cartesian_product import CartesianProductsCategory, cartesian_product
#from sage.categories.functor import ategory
from sage.categories.covariant_functorial_construction import CovariantFunctorialConstruction, CovariantConstructionCategory, RegressiveCovariantConstructionCategory
from sage.categories.algebra_functor import AlgebrasCategory
from sage.categories.dual import DualObjectsCategory
from sage.categories.tensor import TensorProductsCategory, tensor
from sage.categories.morphism import SetMorphism
from sage.misc.cachefunc import cached_method
from sage.structure.element import have_same_parent
from sage.misc.cachefunc import cached_function
from yacop.utils.region import region
from sage.misc.classcall_metaclass import typecall, ClasscallMetaclass
from sage.structure.dynamic_class import dynamic_class

# TODO: combine suspension and truncation into one class to use just one cache (module,grading) -> graded module.

class SuspendedObjectsCategory(CovariantConstructionCategory):

    _functor_category = "SuspendedObjects"

    def _repr_object_names(self):
        """
        EXAMPLES::

            sage: from yacop.categories import YacopLeftModules
            sage: YacopLeftModules(SteenrodAlgebra(3)).SuspendedObjects() # indirect doctest
            Category of suspensions of yacop left modules over mod 3 Steenrod algebra, milnor basis
        """
        return "suspensions of %s"%(self.base_category()._repr_object_names())

def SuspendedObjects(self):
    return SuspendedObjectsCategory.category_of(self)

Category.SuspendedObjects = SuspendedObjects
Category.suspend = SuspendedObjects

def unpickle_suspension(obj,args,kwargs):
    return suspension(obj,*args,**kwargs)

def unpickle_truncation(obj,args,kwargs):
    return truncation(obj,*args,**kwargs)


class SuspendFunctorialConstruction(CovariantFunctorialConstruction):
    """
    """

    _functor_name = "Suspension"
    _functor_category = "SuspendedObjects"

    def _repr_(self):
        return "suspension functor"

    def __call__(self,module,*args,**kwargs):

        # check whether this object/class wants to implement its
        # own creation of suspensions
        if hasattr(module,"SuspendedObjectsFactory"):
           cls = getattr(module,"SuspendedObjectsFactory")
           return cls(module,*args,**kwargs)

        # no custom factory, use default:
        if hasattr(module,"_yacop_grading"):
            # suspension of graded objects
            modorig = module
            grading = module._yacop_grading
            try:
                module = module._yacop_ref
            except AttributeError:
                pass
            grading = suspension(grading,*args,**kwargs)
            res = self.factory(module,grading)
            def unpickle():
               return unpickle_suspension,(modorig,args,kwargs),None
            setattr(res,"__reduce__",unpickle)
            return res

        # suspension of gradings

        if hasattr(module, self._functor_category):
            return getattr(module, self._functor_category)(module,*args,**kwargs)
        raise ValueError("%s is not suspendable" % module)

    @cached_method
    def factory(self,module,grading):

        if module._yacop_grading is grading:
            return module

        # this code is modelled on the unpickling of unique representation objects:
        # we create a clone of the module which we can modify, and we also
        # refine the class to SuspendedObjects if that has been requested
        cls, args, options = module._reduction
        if not hasattr(cls, self._functor_category):
            # create a dummy SuspendedObjects class - is this a good idea?
            #setattr(cls, self._functor_category,cls)
            pass
        else:
            cls = getattr(cls, self._functor_category)

        from copy import copy
        dct = copy(options)
        dct['category'] = module.category().SuspendedObjects()
        N = typecall(cls, *args, **dct)

        # set the grading and the new name
        N._yacop_grading = grading
        N._yacop_ref = module
        N.rename(grading._format_(module))

        # a couple of hacks follow:

        #  - fix variable injection
        if hasattr(N,"gens"):
           def gens():
              return module.gens()
           setattr(N,"gens",gens)
        if hasattr(N,"variables"):
           def variables():
              return module.variables()
           setattr(N,"variables",variables)
        return N


suspension = SuspendFunctorialConstruction()


# we need to make CombinatorialFreeModules of all flavours suspendable

from sage.combinat.free_module import CombinatorialFreeModule

class CombinatorialFreeModules_CartesianProduct_SuspendedObjects(CombinatorialFreeModule.CartesianProduct):

    @staticmethod
    def __classcall_private__(cls,module,*args,**kwopts):
        # turn suspension(sum) into sum(suspensions)
        return cartesian_product(suspension(mod,*args,**kwopts) for mod in module._sets)

CombinatorialFreeModule.CartesianProduct.SuspendedObjects = CombinatorialFreeModules_CartesianProduct_SuspendedObjects



def TruncatedObjects(self):
    return TruncatedObjectsCategory.category_of(self)

Category.TruncatedObjects = TruncatedObjects
Category.truncate = TruncatedObjects

class TruncatedFunctorialConstruction(CovariantFunctorialConstruction):
    """
    """

    _functor_name = "Truncation"
    _functor_category = "TruncatedObjects"

    def _repr_(self):
        return "truncation functor"

    def __call__(self,module,*args,**kwargs):

        # check whether this object/class wants to implement its
        # own creation of truncations
        if hasattr(module,"TruncatedObjectsFactory"):
           cls = getattr(module,"TruncatedObjectsFactory")
           return cls(module,*args,**kwargs)

        # no custom factory, use default:
        if hasattr(module,"_yacop_grading"):
            # truncation of yacop graded objects
            modorig = module
            grading = module._yacop_grading
            try:
                module = module._yacop_ref
            except AttributeError:
                pass
            grading = truncation(grading,*args,**kwargs)
            res = self.factory(module,grading)
            def unpickle():
               return unpickle_truncation,(modorig,args,kwargs),None
            setattr(res,"__reduce__",unpickle)
            return res

        # truncation of gradings

        if hasattr(module, self._functor_category):
            return getattr(module, self._functor_category)(module,*args,**kwargs)
        raise ValueError("%s cannot be truncated" % module)

    @cached_method
    def factory(self,module,grading):
        # this code is modelled on the unpickling of unique representation objects:
        # we create a clone of the module which we can modify, and we also
        # refine the class to SuspendedObjects if that has been requested
        cls, args, options = module._reduction
        if not hasattr(cls, self._functor_category):
           # create a dummy SuspendedObjects class - is this a good idea?
           setattr(cls, self._functor_category,cls)
        cls = getattr(cls, self._functor_category)

        from copy import copy
        dct = copy(options)
        dct['category'] = module.category().TruncatedObjects()
        N = typecall(cls, *args, **dct)

        # set the grading and the new name
        N._yacop_grading = grading
        N._yacop_ref = module
        N.rename(grading._format_(module))

        # a couple of hacks follow:

        #  - fix variable injection
        if hasattr(N,"gens"):
           def gens():
              return module.gens()
           setattr(N,"gens",gens)
        if hasattr(N,"variables"):
           def variables():
              return module.variables()
           setattr(N,"variables",variables)
        return N


truncation = TruncatedFunctorialConstruction()

class TruncatedObjectsCategory(CovariantConstructionCategory):

    _functor_category = "TruncatedObjects"

    def _repr_object_names(self):
        """
        EXAMPLES::

            sage: from yacop.categories import YacopLeftModules
            sage: YacopLeftModules(SteenrodAlgebra(3)).TruncatedObjects() # indirect doctest
            Category of truncations of yacop left modules over mod 3 Steenrod algebra, milnor basis
        """
        return "truncations of %s"%(self.base_category()._repr_object_names())










# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

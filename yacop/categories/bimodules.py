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

from sage.categories.category import Category, CategoryWithParameters
from yacop.categories.left_modules import YacopLeftModules, YacopLeftModuleAlgebras
from yacop.categories.right_modules import YacopRightModules, YacopRightModuleAlgebras
from yacop.categories.common import yacop_category

@yacop_category()
class YacopBimodules(CategoryWithParameters):
    """
    The category of Yacop modules over the Steenrod algebra.

    EXAMPLES::

        sage: from yacop.categories import *
        sage: YacopBimodules(SteenrodAlgebra(7))
        Category of yacop bimodules over mod 7 Steenrod algebra, milnor basis
    """

    def __init__(self, left_base, right_base=None, name=None):
        self._left_base_ring = left_base
        self._right_base_ring = left_base if right_base is None else right_base
        assert self._left_base_ring.characteristic() == self._right_base_ring.characteristic()
        Category.__init__(self, name)

    def _make_named_class_key(self, name):
        return tuple(self.super_categories())

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
        """
        TESTS::

            sage: from yacop.categories import YacopBimodules
            sage: A1 = SteenrodAlgebra(2,profile=(2,1))
            sage: A1.rename("A1")
            sage: A2 = SteenrodAlgebra(2,profile=(3,2,1))
            sage: A2.rename("A2")
            sage: YacopBimodules(A2,A1)
            Category of yacop bimodules over A2 and A1
            sage: YacopBimodules(A1)
            Category of yacop bimodules over A1
        """
        ans = "yacop bimodules over %s" % self._left_base_ring
        if not self._left_base_ring is self._right_base_ring:
            ans += " and %s" % self._right_base_ring
        return ans

    def super_categories(self):
        """
        TESTS::

            sage: from yacop.categories import *
            sage: A1 = SteenrodAlgebra(2,profile=(2,1))
            sage: A1.rename("A1")
            sage: A2 = SteenrodAlgebra(2,profile=(3,2,1))
            sage: A2.rename("A2")
            sage: Y=YacopBimodules(A1,A2)
            sage: Y.super_categories()
            [Category of yacop left modules over A1,
             Category of yacop right modules over A2]

        """
        x = []
        x.append(YacopLeftModules(self._left_base_ring))
        x.append(YacopRightModules(self._right_base_ring))
        return x

    class ParentMethods:
        pass

    class ElementMethods:
        pass

@yacop_category()
class YacopBimoduleAlgebras(CategoryWithParameters):

    def __init__(self, left_base, right_base=None, name=None):
        self._left_base_ring = left_base
        self._right_base_ring = left_base if right_base is None else right_base
        assert self._left_base_ring.characteristic() == self._right_base_ring.characteristic()
        Category.__init__(self, name)

    def _make_named_class_key(self, name):
        return tuple(self.super_categories())

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
        """
        TESTS::

            sage: from yacop.categories import YacopBimoduleAlgebras
            sage: A1 = SteenrodAlgebra(2,profile=(2,1))
            sage: A1.rename("A1")
            sage: A2 = SteenrodAlgebra(2,profile=(3,2,1))
            sage: A2.rename("A2")
            sage: YacopBimoduleAlgebras(A2,A1)
            Category of yacop bimodule algebras over A2 and A1
            sage: YacopBimoduleAlgebras(A2)
            Category of yacop bimodule algebras over A2

        """
        ans = "yacop bimodule algebras over %s" % self._left_base_ring
        if not self._left_base_ring is self._right_base_ring:
            ans += " and %s" % self._right_base_ring
        return ans

    def super_categories(self):
        """
        TESTS::

            sage: from yacop.categories import *
            sage: A1 = SteenrodAlgebra(2,profile=(2,1))
            sage: A1.rename("A1")
            sage: A2 = SteenrodAlgebra(2,profile=(3,2,1))
            sage: A2.rename("A2")
            sage: Y=YacopBimoduleAlgebras(A2,A1)
            sage: Y.super_categories()
            [Category of yacop left module algebras over A2,
             Category of yacop right module algebras over A1]

        """
        x = []
        # adding this leads to C3 troubles:
        #   x.append(YacopBimodules(self._left_base_ring,self._right_base_ring))
        x.append(YacopLeftModuleAlgebras(self._left_base_ring))
        x.append(YacopRightModuleAlgebras(self._right_base_ring))
        return x

    class ParentMethods:
        pass

    class ElementMethods:
        pass

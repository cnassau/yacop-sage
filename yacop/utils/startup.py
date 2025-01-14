# -*- coding: utf-8 -*-

def __startup__():
    import sage.algebras.steenrod.steenrod_algebra
    import types

    def resolution(self, memory=None, filename=None):
        """
        The minimal resolution of the ground field as a module over 'self'.

        TESTS::

            sage: from yacop.resolutions.minres import MinimalResolution
            sage: MinimalResolution(SteenrodAlgebra(7)) is SteenrodAlgebra(7).resolution()
            True
        """
        from yacop.resolutions.minres import MinimalResolution

        return MinimalResolution(self, memory=memory, filename=filename)

    setattr(
        sage.algebras.steenrod.steenrod_algebra.SteenrodAlgebra_generic,
        "resolution",
        resolution,
    )

    def Ext(algebra, M, N=None, filename=None):
        """
        ``Ext(M,N)`` over ``algebra``.
        """
        from yacop.resolutions.smashres import SmashResolution

        assert N is None
        return SmashResolution(M, algebra.resolution(), filename=filename).Homology()

    setattr(sage.algebras.steenrod.steenrod_algebra.SteenrodAlgebra_generic, "Ext", Ext)

    # there are known issues in Sage with pickling of morphisms
    # and we don't want to document the same failures in our test
    # suite.
    from sage.combinat.free_module import CombinatorialFreeModule

    def p_test_pickling(self, tester=None, **options):
        if not hasattr(self, "_can_test_pickling") or self._can_test_pickling():
            tester = self._tester(**options)
            from sage.misc.persist import loads
            from sage.misc.persist import dumps

            tester.assertEqual(loads(dumps(self)), self)
        else:
            tester.info(" (skipped, not picklable) ", newline=False)

    def e_test_pickling(self, tester=None, **options):
        if not hasattr(self, "_can_test_pickling") or self._can_test_pickling():
            tester = self._tester(**options)
            from sage.misc.persist import loads
            from sage.misc.persist import dumps

            tester.assertEqual(loads(dumps(self)), self)
        else:
            tester.info(" (skipped, not picklable) ", newline=False)

    CombinatorialFreeModule._test_pickling = p_test_pickling
    # CombinatorialFreeModule.Element._test_pickling = e_test_pickling (no longer possible, by ticket/22632)

    # workaround for Sage Ticket #13814
    from sage.sets.family import LazyFamily
    from sage.rings.finite_rings.integer_mod_ring import IntegerModRing as Integers

    if LazyFamily(Integers(), lambda i: 2 * i) == LazyFamily(
        Integers(), lambda i: 2 * i
    ):

        def noteq(self, other):
            if self is other:
                return True
            return False

        LazyFamily.__eq__ = noteq

    try:
        16 in LazyFamily(Integers(), lambda i: 2 * i)
    except:
        # we need to overwrite _contains_ in our module base to fix
        # the test suite of SteenrodModuleBase.basis()
        def __contains__(self, x):
            try:
                return self._contains_(x)
            except AttributeError:
                return super(LazyFamily, self).__contains__(x)

        LazyFamily.__contains__ = __contains__

    # workaround for #13811
    from sage.sets.family import AbstractFamily

    def __copy__(self):
        return self

    AbstractFamily.__copy__ = __copy__

    # LazyFamilies cannot be pickled... turn off the resulting noise
    def _test_pickling(self, tester=None, **options):
        pass

    LazyFamily._test_pickling = _test_pickling

    # workaround for Sage ticket #13833
    from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra

    B = SteenrodAlgebra(2, profile=(3, 2, 1))
    A = SteenrodAlgebra(2)
    id = A.module_morphism(codomain=A, on_basis=lambda x: A.monomial(x))
    try:
        x = id(B.an_element())
    except AssertionError:
        from sage.categories.modules_with_basis import ModuleMorphismByLinearity

        origcall = ModuleMorphismByLinearity.__call__

        def call(self, *args):
            before = args[0 : self._position]
            after = args[self._position + 1 : len(args)]
            x = args[self._position]
            nargs = before + (self.domain()(x),) + after
            return origcall(self, *nargs)

        ModuleMorphismByLinearity.__call__ = call

    # workaround for Sage ticket #18449
    from sage.sets.set_from_iterator import EnumeratedSetFromIterator
    from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
    from sage.categories.infinite_enumerated_sets import InfiniteEnumeratedSets
    from sage.categories.enumerated_sets import EnumeratedSets
    from sage.rings.integer_ring import ZZ

    C = CombinatorialFreeModule(ZZ, EnumeratedSetFromIterator(Integers))
    if False and sage.categories.tensor.tensor((C,)).basis() in FiniteEnumeratedSets():

        def __init_18449__(self, set, function, name=None):
            """
            patched __init__ function from ticket #18449
            """
            from sage.combinat.combinat import CombinatorialClass  # workaround #12482
            from sage.structure.parent import Parent

            category = EnumeratedSets()
            if set in FiniteEnumeratedSets():
                category = FiniteEnumeratedSets()
            elif set in InfiniteEnumeratedSets():
                category = InfiniteEnumeratedSets()
            elif isinstance(set, (list, tuple)):
                category = FiniteEnumeratedSets()
            elif isinstance(set, CombinatorialClass):
                try:
                    if set.is_finite():
                        category = FiniteEnumeratedSets()
                except NotImplementedError:
                    pass
            Parent.__init__(self, category=category)
            from copy import copy

            self.set = copy(set)
            self.function = function
            self.function_name = name

        LazyFamily.__init__ = __init_18449__

    # use a lower max_runs value for the TestSuite
    from sage.misc.sage_unittest import InstanceTester

    InstanceTester.__init_original__ = InstanceTester.__init__

    def newinit(self, *args, **kwds):
        self.__init_original__(*args, **kwds)
        self._max_runs = 40

    InstanceTester.__init__ = newinit

    # fix a problem for __contain__ in Categories_over_base_ring
    # when more than one base is involved:
    from sage.categories.category import Category
    from sage.categories.category_types import Category_over_base_ring
    from sage.categories.modules import Modules
    from sage.categories.algebras import Algebras
    from sage.categories.modules_with_basis import ModulesWithBasis
    from sage.rings.finite_rings.finite_field_constructor import GF

    C = CombinatorialFreeModule(
        GF(5), ZZ, category=(ModulesWithBasis(GF(5)), Algebras(ZZ))
    )
    if C not in Modules(ZZ):
        _sagecode = Category_over_base_ring.__contains__
        Category_over_base_ring.__contains_sage__ = _sagecode
        def __contains_yacop__(self, Z):
            ans = self.__contains_sage__(Z)
            if not ans:
                try:
                    ans = self in Z.categories()
                except:
                    pass
            return ans

        Category_over_base_ring.__contains__ = __contains_yacop__

    # Sage insists that Subquotients of CartesianProducts are again CartesianProducts
    # (and similarly for TensorProducts). We forcefully disagree:
    from sage.categories.covariant_functorial_construction import RegressiveCovariantConstructionCategory
    @classmethod
    def default_super_categories_yacop(cls, category, *args):
        """
        TESTS::

            sage: import yacop

            sage: # an earlier version of this hack broke the MRO for quasi symmetric functions:
            sage: QuasiSymmetricFunctions(GF(3))
            Quasisymmetric functions over the Finite Field of size 3

        """
        sageresult = Category.join([category, super(RegressiveCovariantConstructionCategory, cls).default_super_categories(category, *args)])
        ans = sageresult
        if isinstance(ans, sage.categories.category.JoinCategory):
            j = [cat for cat in sageresult.super_categories() if not hasattr(cat,"yacop_no_default_inheritance")]
            ans = Category.join(j)
        return ans
    RegressiveCovariantConstructionCategory.default_super_categories = default_super_categories_yacop

def __print_banner__():
    import yacop
    from sage.env import SAGE_BANNER

    if SAGE_BANNER.lower() == "no":
        return
    bars = "─" * 68
    s = []
    a = s.append
    a("┌" + bars + "┐")
    a("\n│ %-66s │\n" % ("Imported package Yacop (version %s)" % yacop.__version__))
    a("└" + bars + "┘")
    print("".join(s))

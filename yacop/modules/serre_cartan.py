r"""
A base class for Steenrod algebra modules that are given by a list of generators
together with the action of the Sq^j (or beta, P^j).

AUTHORS: - Christian Nassau

EXAMPLES AND TESTS:

TESTS::

    sage: # create a piece of RP^infty as a SerreCartanModule
    sage: from yacop.modules.serre_cartan import SerreCartanModule
    sage: basis = [("a%d"%_,_) for _ in range(5,13)]
    sage: M = SerreCartanModule(SteenrodAlgebra(2),basis) ; M
    Free module generated by [a5, a6, a7, a8, a9, a10, a11, a12] over Finite Field of size 2
    sage: M.bbox()
    region(e = 0, s = 0, 5 <= t <= 12)
    sage: sorted(list(M.graded_basis()))
    [a10, a11, a12, a5, a6, a7, a8, a9]
    sage: M.inject_variables()
    Defining a5, a6, a7, a8, a9, a10, a11, a12
    sage: M.set_operations([
    ....:     (Sq(1), a5, a6), (Sq(4), a5, a9), (Sq(5), a5, a10),
    ....:     (Sq(2), a6, a8), (Sq(4), a6, a10), (Sq(6), a6, a12),
    ....:     (Sq(1), a7, a8), (Sq(2), a7, a9), (Sq(3), a7, a10),
    ....:     (Sq(4), a7, a11), (Sq(5), a7, a12), (Sq(1), a9, a10),
    ....:     (Sq(2), a10, a12), (Sq(1), a11, a12)])
    sage: for elem in (a5,a7):
    ....:     for op in SteenrodAlgebra(2,profile=(3,2,1)).basis():
    ....:         act=op*elem
    ....:         if not act.is_zero():
    ....:             print("%-10s * %-3s = %s" % (op,elem,act))
    1          * a5  = a5
    Sq(1)      * a5  = a6
    Sq(0,1)    * a5  = a8
    Sq(4)      * a5  = a9
    Sq(5)      * a5  = a10
    Sq(0,0,1)  * a5  = a12
    Sq(4,1)    * a5  = a12
    1          * a7  = a7
    Sq(1)      * a7  = a8
    Sq(2)      * a7  = a9
    Sq(0,1)    * a7  = a10
    Sq(3)      * a7  = a10
    Sq(4)      * a7  = a11
    Sq(2,1)    * a7  = a12
    Sq(5)      * a7  = a12

    sage: M("a6") == a6
    True

    sage: # test truncations
    sage: from yacop.categories.functors import truncation
    sage: N = truncation(M, tmin=7, tmax=11)
    sage: sorted(list(N.graded_basis()))
    [a10, a11, a7, a8, a9]
    sage: N.bbox()
    region(e = 0, s = 0, 7 <= t <= 11)
    sage: [(x,x in M, x in N) for x in M.gens()]
    [(a5, True, False),
     (a6, True, False),
     (a7, True, True),
     (a8, True, True),
     (a9, True, True),
     (a10, True, True),
     (a11, True, True),
     (a12, True, True)]
    sage: [N(x) for x in (a7, a8, a9, a10, a11, a12)]
    [a7, a8, a9, a10, a11, 0]
    sage: N(a6)
    Traceback (most recent call last):
    ...
    ValueError: cannot cast a6 to Free module generated by [a7, a8, a9, a10, a11] over Finite Field of size 2
    sage: Sq(2)*N(a7)
    a9
    sage: Sq(2,1)*N(a7)
    0

CLASS DOCUMENTATION:

"""

# *****************************************************************************
#       Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#  Distributed under the terms of the GNU General Public License (GPL)
# *****************************************************************************
from sage.algebras.all import SteenrodAlgebra, Sq
from sage.misc.cachefunc import cached_method
from yacop.categories import YacopLeftModules
from yacop.utils.gradings import YacopGradingFromDict
from yacop.utils.region import region
from yacop.modules.module_base import SteenrodModuleBase, SteenrodModuleGrading
from yacop.utils.finite_graded_set import FiniteGradedSet
from copy import copy


class SerreCartanModuleBase(SteenrodModuleBase):
    def __init__(self, basis, grading=None, category=None):
        SteenrodModuleBase.__init__(self, basis, grading=grading, category=category)
        self._SCA = SteenrodAlgebra(self._prime, basis="serre-cartan")
        self._SCM = SteenrodAlgebra(self._prime, basis="milnor")

    @cached_method
    def left_steenrod_action_milnor(self, a, m):
        # check whether result is zero for dimensional reasons
        # FIXME: implement this
        smds = []
        # transform to Serre-Cartan basis
        for (key, cf) in self._SCA(self._SCM.monomial(a)):
            # FIXME: as is, this works only for p=2
            m2 = self.monomial(m)
            for exponent in reversed(key):
                m2 = self.linear_combination(
                    (self.left_steenrod_action_serre_cartan(exponent, keym2), cfm2)
                    for (keym2, cfm2) in m2
                )
            smds.append((m2, cf))
        return self.linear_combination(smds)


class SerreCartanModule(SerreCartanModuleBase):
    """

    TESTS::

        sage: from yacop.modules.serre_cartan import SerreCartanModule
        sage: basis = [("x0",0), ("x4",4), ("x6",6), ("x7",7), ("x10", 10)]
        sage: M = SerreCartanModule(SteenrodAlgebra(2),basis) ; M
        Free module generated by [x0, x4, x6, x7, x10] over Finite Field of size 2
        sage: sorted(list(M.graded_basis(tmin=3,tmax=6)))
        [x4, x6]
        sage: M.inject_variables()
        Defining x0, x4, x6, x7, x10
        sage: Sq(0)*x0, Sq(4)*x0
        (x0, 0)
        sage: M.set_operation(Sq(4),x0,x4)
        sage: Sq(4)*x0
        x4
        sage: M.set_operations([
        ....:    (Sq(2),x4,x6), (Sq(1),x6,x7), (Sq(4),x6,x10)
        ....: ])
        sage: Sq(7)*x0
        0



    """

    @staticmethod
    def __classcall_private__(
        cls, basering, basis, operations=None, latexnames=None, category=None
    ):
        basis = tuple(basis)
        if latexnames is None:
            latexnames = ()
        return super(SerreCartanModule, cls).__classcall__(
            cls,
            basering,
            basis,
            operations=operations,
            latexnames=latexnames,
            category=category,
        )

    def __init__(
        self, basering, basis, operations=None, latexnames=None, category=None
    ):
        if category is None:
            category = YacopLeftModules(basering)
        dct = dict()
        grades = dict()
        items = []
        for itm in basis:
            edeg = 0
            sdeg = 0
            if len(itm) == 2:
                elem, tdeg = itm
            elif len(itm) == 3:
                elem, tdeg, edeg = itm
            elif len(itm) == 4:
                elem, tdeg, edeg, sdeg = itm
            else:
                raise ValueError("item %s to understood" % itm)
            if elem in items:
                raise ValueError("duplicate item in basis")
            items.append(elem)
            grades[elem] = (tdeg, edeg, sdeg)
            reg = region(s=sdeg, e=edeg, t=tdeg)
            try:
                u = dct[reg]
            except KeyError:
                u = []
            u.append(elem)
            dct[reg] = u
        # grading = YacopGradingFromDict((k,tuple(v)) for (k,v) in dct.iteritems())
        self._latex_names = dict(latexnames)
        grbasis = FiniteGradedSet(items, tesfunc=lambda x: grades[x])
        grading = SteenrodModuleGrading(grbasis, self)
        SerreCartanModuleBase.__init__(
            self, grbasis, grading=grading, category=category
        )
        # self.monomial is only available after refining the category, so we can
        # only set the proper grading now
        # grading = YacopGradingFromDict((k,tuple(self.monomial(_) for _ in v)) for (k,v) in dct.iteritems())
        # self._set_grading(grading)

        self._assign_names([str(_) for _ in items])
        self._ops = dict()
        if not operations is None:
            self.set_operations(operations)

        # list of keys that we accept in the element constructor
        # this can become bigger than the original keys if we deal
        # with a truncation where certain keys are to be treated as zero
        self._coerce_keys = list(self.basis().keys())

    def gens(self):
        return [self.monomial(x) for x in self.basis().keys()]

    def _basis(self):
        ans = []
        for g in self.gens():
            ans.append((str(g), g.t, g.e, g.s))
        return ans

    def operations(self):
        """
        FIXME: needs doctest
        """
        return [(Sq(i), self(j), k) for ((i, j), k) in self._ops.items()]

    def _repr_term(self, x):
        return str(x)

    def _latex_term(self, x):
        try:
            return self._latex_names[x]
        except:
            return self._repr_term(x)

    def set_operation(self, op, src, dst, clear_cache=True):
        cnt = 0
        for (key, cf) in self._SCA(op):
            if cnt > 0 or len(key) != 1:
                raise ValueError("operation must be a Sq^j or P^j or the Bockstein")
            cnt += 1
        assert src.parent() is self
        assert dst.parent() is self
        assert len(src.monomials()) == 1
        ((skey, scf),) = src
        self._ops[(key[0], skey)] = cf / scf * dst
        if clear_cache:
            self.left_steenrod_action_milnor.clear_cache()

    def set_operations(self, operations):
        for (op, src, dst) in operations:
            self.set_operation(op, src, dst, clear_cache=False)
        self.left_steenrod_action_milnor.clear_cache()

    def left_steenrod_action_serre_cartan(self, exp, key):
        if exp == 0:
            return self.monomial(key)
        try:
            return self._ops[(exp, key)]
        except KeyError:
            return self.zero()

    def __contains__(self, x):
        try:
            if x.parent() is self:
                return True
        except:
            pass
        if hasattr(x, "monomials") and all(_ in self._coerce_keys for (_, cf) in x):
            return True
        if x in list(self.basis().keys()):
            return True
        return False

    def _element_constructor_(self, x):
        try:
            if x.parent() is self:
                return x
        except:
            pass
        if hasattr(x, "monomials") and all(_ in self._coerce_keys for (_, cf) in x):
            # keys from self._coerce_keys setminus self.basis().keys() map to zero
            return self._from_dict(
                {key: cf for (key, cf) in x if key in list(self.basis().keys())}
            )
        if x in list(self.basis().keys()):
            return self.monomial(x)
        elif x in self._coerce_keys:
            return self.zero()
        try:
            if x.is_zero():
                return self.zero()
        except:
            pass
        if False:
            print(
                "x=",
                x,
                "type",
                type(x),
                "keys=",
                list(self.basis().keys()),
                "ckeys=",
                self._coerce_keys,
            )
            print("list(x)=", list(x))
            return self.zero()
        raise ValueError("cannot cast %s to %s" % (x, self))

    def _xxcoerce_map_from_(self, S):
        if isinstance(S, SerreCartanModule):
            return True

    @staticmethod
    def SuspendedObjectsFactory(module, *args, **kwopts):
        """
        TESTS::

            sage: from yacop.modules.serre_cartan import SerreCartanModule
            sage: from yacop.modules.projective_spaces import ComplexProjectiveSpace
            sage: M = SerreCartanModule.Clone(ComplexProjectiveSpace(botexp=3,topexp=7),letter='f') ; M
            Free module generated by [f6, f8, f10, f12, f14] over Finite Field of size 2
            sage: for m in M.graded_basis():
            ....:     print((m,[Sq(i)*m for i in range(5)]))
            (f6, [f6, 0, f8, 0, f10])
            (f8, [f8, 0, 0, 0, 0])
            (f10, [f10, 0, f12, 0, 0])
            (f12, [f12, 0, 0, 0, 0])
            (f14, [f14, 0, 0, 0, 0])
            sage: from yacop.categories.functors import suspension
            sage: N = suspension(M,s=2,t=3)
            sage: for n in N.graded_basis():
            ....:     print((n.s,n.e,n.t,n))
            (2, 0, 9, f6)
            (2, 0, 11, f8)
            (2, 0, 13, f10)
            (2, 0, 15, f12)
            (2, 0, 17, f14)
            sage: for n in N.graded_basis():
            ....:     print((n,[Sq(i)*n for i in range(5)]))
            (f6, [f6, 0, f8, 0, f10])
            (f8, [f8, 0, 0, 0, 0])
            (f10, [f10, 0, f12, 0, 0])
            (f12, [f12, 0, 0, 0, 0])
            (f14, [f14, 0, 0, 0, 0])

        """
        # FIXME: why does the category framework not handle this
        # FIXME: the internal differential is lost (?)
        limits = region(kwopts)
        t, s, e = 0, 0, 0
        try:
            s = limits.s
        except:
            pass
        try:
            t = limits.t
        except:
            pass
        try:
            e = limits.e
        except:
            pass
        newbasis = [
            (key, tdeg + t, edeg + e, sdeg + s)
            for (key, tdeg, edeg, sdeg) in module._basis()
        ]
        ans = SerreCartanModule(
            module._yacop_base_ring,
            newbasis,
            latexnames=tuple(module._latex_names.items()),
        )
        newops = [(a, ans(x), ans(y)) for (a, x, y) in module.operations()]
        ans.set_operations(newops)
        return ans

    @staticmethod
    def TruncatedObjectsFactory(module, *args, **kwopts):
        """
        TESTS::

            sage: from yacop.modules.serre_cartan import SerreCartanModule
            sage: from yacop.modules.projective_spaces import ComplexProjectiveSpace
            sage: M = SerreCartanModule.Clone(ComplexProjectiveSpace(botexp=3,topexp=7),letter='f') ; M
            Free module generated by [f6, f8, f10, f12, f14] over Finite Field of size 2
            sage: from yacop.categories.functors import truncation
            sage: N = truncation(M,tmin=8, tmax=12) ; N
            Free module generated by [f8, f10, f12] over Finite Field of size 2
            sage: N.coerce_embedding()
            Generic morphism:
                From: Free module generated by [f8, f10, f12] over Finite Field of size 2
                To:   Free module generated by [f6, f8, f10, f12, f14] over Finite Field of size 2
            sage: for g in N.graded_basis():
            ....:     print("%-3s -> %s" % (g,M(g)))
            ....:     assert(g == N(M(g)))
            ....:     assert(M(g) == M(N(M(g))))
            f8  -> f8
            f10 -> f10
            f12 -> f12

            sage: N2 = truncation(M,tmin=8, tmax=12) ;# make sure it can be constructed a second time
            sage: N is N2
            True

        """
        # FIXME: why does the category framework not handle this
        # FIXME: the internal differential is lost (?)
        limits = region(kwopts)
        tmin, tmax = limits.trange
        smin, smax = limits.srange
        emin, emax = limits.erange
        gens = [(k, module.monomial(k)) for k in list(module.basis().keys())]
        tbasis = [
            (k, g.t, g.e, g.s)
            for (k, g) in gens
            if g.t >= tmin
            and g.t <= tmax
            and g.s >= smin
            and g.s <= smax
            and g.e >= emin
            and g.e <= emax
        ]
        ans = SerreCartanModule(module._yacop_base_ring, tbasis)
        if not hasattr(ans,"_yacop_sc_truncation"):
            # the SerreCartanModule class has unqiue representation, so if
            # we construct the same truncation twice we might already have
            # a completely constructed ans here (and re-registering the embedding
            # will fail). we use a dummy attribute to detect this situation
            emb = ans.module_morphism(codomain=module, on_basis=module.monomial)
            ans.register_embedding(emb)
            conv = module.module_morphism(codomain=ans, function=ans._element_constructor_)
            ans.register_conversion(conv)
            ans._coerce_keys += [k for (k, g) in gens if g.t > tmax]
            ans._ops = {
                (op, m): ans(n)
                for ((op, m), n) in module._ops.items()
                if m in list(ans.basis().keys()) and not ans(n).is_zero()
            }
            ans._yacop_sc_truncation = True
        return ans

    @staticmethod
    def Clone(
        module,
        reg=None,
        names="{letter}{tdeg}{abasnum}",
        latex="{letter}_{{{tdeg}{abasnum}}}",
        letter="g",
    ):
        """
        Clone some other module as a SerreCartan module. This can be used
        to produce a better performing version of another module, or to
        create a smaller description of it.

        TESTS::

            sage: from yacop.modules.serre_cartan import SerreCartanModule
            sage: from yacop.modules.projective_spaces import ComplexProjectiveSpace
            sage: M = SerreCartanModule.Clone(ComplexProjectiveSpace(botexp=-7,topexp=-3),letter='f') ; M
            Free module generated by [f14, f12, f10, f8, f6] over Finite Field of size 2
            sage: M.inject_variables()
            Defining f14, f12, f10, f8, f6
            sage: for g in sorted(M.graded_basis()):
            ....:     for i in range(1,10):
            ....:         h = Sq(i)*g
            ....:         if not h.is_zero():
            ....:             print("  %-5s * %3s = %s" % (Sq(i),g,h))
            Sq(2) * f10 = f8
            Sq(4) * f10 = f6
            Sq(4) * f12 = f8
            Sq(2) * f14 = f12
            sage: cmap1 = M.cloning_map() ; cmap1
            Generic morphism:
                From: mod 2 cohomology of complex projective space P^{-3}_{-7}
                To:   Free module generated by [f14, f12, f10, f8, f6] over Finite Field of size 2
            sage: cmap2 = M.cloning_map_reverse(); cmap2
            Generic morphism:
                From: Free module generated by [f14, f12, f10, f8, f6] over Finite Field of size 2
                To:   mod 2 cohomology of complex projective space P^{-3}_{-7}
            sage: for g in sorted(M.graded_basis()):
            ....:     print("-     %3s  <-  %5s  -> %-3s" % (g,cmap2(g),cmap1(cmap2(g))))
            -     f10  <-  x^(-5)  -> f10
            -     f12  <-  x^(-6)  -> f12
            -     f14  <-  x^(-7)  -> f14
            -      f6  <-  x^(-3)  -> f6
            -      f8  <-  x^(-4)  -> f8

            sage: from yacop.modules.dual_steenrod_algebra import DualSteenrodAlgebra
            sage: from yacop.categories.functors import suspension
            sage: from yacop.modules.morph_module import SubModule
            sage: D = DualSteenrodAlgebra(2)
            sage: D.inject_variables()
            Defining xi
            sage: A1 = suspension(SubModule(D,(xi[1]**3*xi[2],)),t=6)
            sage: A1clone = SerreCartanModule.Clone(A1,letter='b') ; A1clone
            Free module generated by [b0, b1, b2, b3a, b3b, b4, b5, b6] over Finite Field of size 2
            sage: A1clone.inject_variables()
            Defining b0, b1, b2, b3a, b3b, b4, b5, b6
            sage: Sq(3,1)*b0
            b6
            sage: A1(Sq(4)*b0), Sq(4)*A1(b0)
            ((xi[1]**2)*S(6,0,0), (xi[1]**2)*S(6,0,0))
            sage: A1(b5+b2)
            (xi[1] + xi[1]*xi[2] + xi[1]**4)*S(6,0,0)
            sage: A1clone(Sq(3)*A1(b0))
            b3a + b3b

        """
        limits = module.bbox().intersect(region(reg))
        degrees = {}
        for _ in module.graded_basis(limits):
            for d in _.homogeneous_decomposition():
                degrees[d] = 1
        signindic = lambda s: "pos" if s > 0 else "neg" if s < 0 else ""
        clonedict = {}
        map = {}
        elems = []
        ops = []
        A = module._yacop_base_ring
        ldict = {}
        for deg in sorted(degrees):
            bas = []
            gb = list(module.graded_basis(deg))
            for (num, elem) in enumerate(gb):
                if len(gb) > 1:
                    abasnum = chr(ord("a") + num)
                else:
                    abasnum = ""
                # sdegrees 0,1,.. map to a,b,c... negative homological degrees use Z,Y,X,...
                sletter = (
                    chr(ord("a") + elem.s)
                    if elem.s >= 0
                    else chr(ord("Z") + elem.s + 1)
                )
                origname = str(elem)
                name = names.format(
                    tdeg=abs(elem.t),
                    sdeg=abs(elem.s),
                    edeg=abs(elem.e),
                    repr=str(elem),
                    tsgn=signindic(elem.t),
                    esgn=signindic(elem.e),
                    ssgn=signindic(elem.s),
                    basnum=num,
                    abasnum=abasnum,
                    letter=letter,
                    sletter=sletter,
                    origname=origname,
                )
                lname = latex.format(
                    tdeg=abs(elem.t),
                    sdeg=abs(elem.s),
                    edeg=abs(elem.e),
                    repr=str(elem),
                    tsgn=signindic(elem.t),
                    esgn=signindic(elem.e),
                    ssgn=signindic(elem.s),
                    basnum=num,
                    abasnum=abasnum,
                    letter=letter,
                    sletter=sletter,
                    origname=origname,
                )
                elems.append((name, deg.t, deg.e, deg.s))
                bas.append(name)
                ldict[name] = lname
                clonedict[name] = elem
            map[deg] = bas
        ans = SerreCartanModuleClone(
            module, tuple(elems), latexnames=tuple(ldict.items())
        )
        for deg in degrees:
            gb = list(module.graded_basis(deg))
            for (num, elem) in enumerate(gb):
                thisbasis = map[deg]
                curelem = ans(thisbasis[num])
                for i in range(1, limits.tmax - deg.t + 1):
                    op = A.Sq(i)
                    x = op * elem
                    if not x.is_zero():
                        # print "op",op,elem,x
                        tardeg = x.degree()
                        try:
                            tarbasis = map[tardeg]
                            coeffs = module.graded_basis_coefficients(x, tardeg)
                            # print "coeffs",coeffs
                            x2 = ans.linear_combination(
                                (ans(key), cf) for (cf, key) in zip(coeffs, tarbasis)
                            )
                            ops.append((op, curelem, x2))
                        except KeyError:
                            pass
        ans.set_operations(ops)
        ans._set_cloning_map(module, clonedict, map)
        # module.register_coercion(ans.cloning_map_reverse())
        return ans


class SerreCartanModuleClone(SerreCartanModule):
    def __init__(self, module, basis, operations=None, latexnames=None, category=None):
        basering = module._yacop_base_ring
        SerreCartanModule.__init__(
            self,
            basering,
            basis,
            operations=operations,
            latexnames=latexnames,
            category=category,
        )
        self._cloning_map_reverse = self.module_morphism(
            codomain=module, on_basis=self._to_clone_source
        )
        self._cloning_map = module.module_morphism(
            codomain=self, function=self._from_clone_source
        )
        self.register_embedding(copy(self.cloning_map_reverse()))
        self.register_coercion(copy(self.cloning_map()))

    def _set_cloning_map(self, module, cdict, map):
        self._cloning_origin = module
        self._cloning_dict = cdict
        self._basis_by_degree = map

    def _to_clone_source(self, key):
        return self._cloning_dict[key]

    def _from_clone_source(self, elem):
        if elem.is_zero():
            return self.zero()
        ans = []
        for (deg, smd) in elem.homogeneous_decomposition().items():
            try:
                b = self._basis_by_degree[deg]
                coeffs = self._cloning_origin.graded_basis_coefficients(elem, deg)
                for (cf, key) in zip(coeffs, b):
                    ans.append((self(key), cf))
            except KeyError:
                pass
        return self.linear_combination(ans)

    @cached_method
    def cloning_map(self):
        return self._cloning_map

    @cached_method
    def cloning_map_reverse(self):
        return self._cloning_map_reverse

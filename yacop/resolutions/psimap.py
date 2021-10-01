r"""
The map psi : D* -> D^infty* that defines an A-modules structure on an A(n)-resolution.

AUTHORS: - Christian Nassau (2011-05-13: version 1.0)

CLASS DOCUMENTATION:
"""

# *****************************************************************************
#       Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#  Distributed under the terms of the GNU General Public License (GPL)
# *****************************************************************************

from tkinter import Tcl
from yacop.utils.tcl import Yacop
from yacop.utils.region import region
from sage.structure.element import Element
from yacop.categories import YacopLeftModules, YacopGradedSets
from threading import Thread
from yacop.modules.free_modules import FreeModuleImpl
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.parent import Parent
from sage.rings.infinity import Infinity
from sage.categories.objects import Objects
from sage.categories.all import (
    EnumeratedSets,
    FiniteEnumeratedSets,
    InfiniteEnumeratedSets,
    Sets,
)
from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra
from sage.misc.cachefunc import cached_method


class PsiMap(Parent, UniqueRepresentation):
    """
    Given a sub Hopf algebra B=A(N) of the Steenrod algebra A and a minimal B-resolution D*,
    a psi map is an A-linear map
          psi : A \tensor_B D* -> Dual(A) \tensor_B D*
    such that the image of psi is an A-linear resolution of the ground field that is B-isomorphic to D*.
    """

    @staticmethod
    def __classcall_private__(cls, resolution, filename=None, memory=None):
        if not isinstance(resolution, MinimalResolution):
            raise ValueError("first argument must be a minimal resolution")
        if filename is None:
            filename = ""
        if memory:
            pass
        return super(GFR, cls).__classcall__(cls, algebra, filename)

    def __init__(self, algebra, filename):
        """
        .. autoclass:: GFR
        """
        self.tcl = Yacop.Interpreter()
        self._filename = filename
        self._algebra = algebra

        self._profmode = "auto"
        self._viewtype = "odd" if algebra.is_generic() else "even"

        # test whether prime is supported
        self.tcl.eval("steenrod::prime %s inverse 1" % algebra.prime())

        self._profile = tclprofile(algebra)

        self.tcl.eval("set p %d;set alg {%s}" % (algebra.prime(), self._profile))

        self.tcl.eval(
            """
                 yacop::gfr create resolution {%s}
                 if {[info exists alg]} {
                    resolution algebra $p $alg
                 }
                 array set resinfo [resolution algebra]
                 if {$resinfo(prime) eq ""} {
                    error "cannot deduce the prime/algebra of this resolution"
                 }
                 set resinfo(viewtype) %s
                 resolution viewtype $resinfo(viewtype)
            """
            % (self._filename, self._viewtype)
        )

        self._prime = int(self.tcl.eval("set resinfo(prime)"))
        self._profile = self.tcl.eval("set resinfo(algebra)")
        self._viewtype = self.tcl.eval("set resinfo(viewtype)")
        self._quiet = True

        Parent.__init__(self, category=Sets())

    def Chart(self):
        from yacop.resolutions.charter import Charter

        return Charter(self._filename, self._viewtype)

    def _repr_(self):
        return "minimal resolution of %s" % self._algebra

    def is_complete(self, s, n):
        """
        Check whether the bidegree has been computed

        TESTS::

            sage: from yacop.resolutions.minres import GFR
            sage: C=GFR(SteenrodAlgebra(2),memory=True)
            sage: C.extend(s=3,n=4)
            sage: matrix([[1 if C.is_complete(s,n) else 0 for n in (0,..,7)] for s in reversed([0,..,5])])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [1 1 1 1 1 0 0 0]
            [1 1 1 1 1 0 0 0]
            [1 1 1 1 1 0 0 0]
            [1 1 1 1 1 1 1 1]

            sage: C=GFR(SteenrodAlgebra(2,generic=True),memory=True)
            sage: C.extend(s=3,n=4)
            sage: matrix([[1 if C.is_complete(s,n) else 0 for n in (0,..,7)] for s in reversed([0,..,5])])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [1 1 1 1 1 0 0 0]
            [1 1 1 1 1 0 0 0]
            [1 1 1 1 1 0 0 0]
            [1 1 1 1 1 1 1 1]

            sage: C=GFR(SteenrodAlgebra(5),memory=True)
            sage: C.extend(s=3,n=4)
            sage: matrix([[1 if C.is_complete(s,n) else 0 for n in (0,..,7)] for s in reversed([0,..,5])])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [1 1 1 1 1 0 0 0]
            [1 1 1 1 1 0 0 0]
            [1 1 1 1 1 0 0 0]
            [1 1 1 1 1 1 1 1]
        """
        if s <= 0:
            return True
        t = s + n
        if self._viewtype == "even":
            t = 2 * t
        res = self.tcl.eval("resolution isComplete %d %d" % (s, t))
        if eval(res):
            return True
        return False

    def extend(self, reg=None, **kwargs):
        """
        Extend the resolution to the indicated bidegree.

        TESTS::

            sage: from yacop.resolutions.minres import GFR
            sage: C=GFR(SteenrodAlgebra(2),memory=True)
            sage: C.extend(s=3,t=6)
            sage: matrix([[1 if C.is_complete(s,n) else 0 for n in (0,..,7)] for s in reversed([0,..,5])])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [1 1 1 1 0 0 0 0]
            [1 1 1 1 1 0 0 0]
            [1 1 1 1 1 1 0 0]
            [1 1 1 1 1 1 1 1]

            sage: C=GFR(SteenrodAlgebra(2,generic=True),memory=True)
            sage: C.extend(s=3,t=6)
            sage: matrix([[1 if C.is_complete(s,n) else 0 for n in (0,..,7)] for s in reversed([0,..,5])])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [1 1 1 1 0 0 0 0]
            [1 1 1 1 1 0 0 0]
            [1 1 1 1 1 1 0 0]
            [1 1 1 1 1 1 1 1]

            sage: C=GFR(SteenrodAlgebra(5),memory=True)
            sage: C.extend(s=3,t=6)
            sage: matrix([[1 if C.is_complete(s,n) else 0 for n in (0,..,7)] for s in reversed([0,..,5])])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [1 1 1 1 0 0 0 0]
            [1 1 1 1 1 0 0 0]
            [1 1 1 1 1 1 0 0]
            [1 1 1 1 1 1 1 1]
        """
        quiet = kwargs.pop("quiet", True)
        if reg is None:
            reg = region()
        reg = reg.intersect(region(kwargs))
        assert reg.smax < Infinity or reg.tmax < Infinity
        bounds = ""
        if reg.smax < Infinity:
            bounds += " sdeg %d" % reg.smax
        else:
            bounds += " sdeg %d" % reg.tmax
        if reg.nmax < Infinity:
            if self._viewtype == "even":
                bounds += " rtdeg %d" % reg.nmax
            else:
                bounds += " tdeg %d" % reg.nmax
        if reg.tmax < Infinity:
            if self._viewtype == "even":
                bounds += " ideg %d" % (2 * reg.tmax)
            else:
                bounds += " ideg %d" % reg.tmax
        if quiet is None:
            quiet = self._quiet
        if quiet:
            self.tcl.eval("yacop::sectionizer quiet on")
        else:
            self.tcl.eval("yacop::sectionizer quiet off")
        self.tcl.eval(
            """
              resolution profmode %s
              resolution extend-to {%s}
           """
            % (self._profmode, bounds)
        )

    def generators(self, region, extracondition=""):
        """
        Search for generators in the given region.
        Meaningful region attributes are `s`, `t`, `n=t-s`, `b=s-e`

        TESTS::

            sage: from yacop.resolutions.minres import GFR
            sage: from yacop.utils.region import region
            sage: def count(C,**args): return len(C.generators(region(args)))
            sage: C=GFR(SteenrodAlgebra(3),memory=True)
            sage: C.extend(s=10,n=20)
            sage: count(C,n=11),count(C,t=13),count(C,s=2),count(C,s=2,e=1)
            (3, 2, 5, 2)
            sage: C=GFR(SteenrodAlgebra(2,generic=True),memory=True)
            sage: C.extend(s=10,n=20)
            sage: count(C,n=11),count(C,t=13),count(C,s=2),count(C,s=2,e=1)
            (6, 1, 10, 3)
            sage: C=GFR(SteenrodAlgebra(2),memory=True)
            sage: C.extend(s=10,n=20)
            sage: count(C,n=11),count(C,t=13),count(C,s=2),count(C,s=2,e=1)
            (3, 1, 10, 0)
            sage: count(C)
            66
        """
        from tkinter import TclError

        def cond(var, col, fac=1):
            res = ""
            mi, ma = region.min(var), region.max(var)
            if mi > -Infinity:
                res += " and %s >= %d" % (col, fac * mi)
            if ma < +Infinity:
                res += " and %s <= %d" % (col, fac * ma)
            return res

        c = ""
        c += cond("s", "sdeg")
        c += cond("t", "ideg")
        c += cond("n", "ndeg")
        c += cond("e", "edeg")
        c += cond("b", "(sdeg-edeg)")
        if len(c) and len(extracondition):
            c += " and "
        c += extracondition
        while c[:4] == " and":
            c = c[4:]
        if len(c) and c[:5] != "where":
            c = "where " + c
        try:
            res = (
                "["
                + self.tcl.eval(
                    """
               join [resolution db eval {
                   select pydict('id',rowid,'s',sdeg,'t',ideg,'e',edeg,'n',ndeg,'num',basid) from chart_generators %s
               }] ,
            """
                    % c
                )
                + "]"
            )
        except TclError as e:
            raise TclError("query failed: %s\n%s" % (c, e.message))
        return eval(res)

    def an_element(self):
        """
        TESTS::

            sage: from yacop.resolutions.minres import GFR
            sage: C=GFR(SteenrodAlgebra(13),memory=True)
            sage: C.extend(s=2,n=30)
            sage: C.an_element() # random
        """
        return self.generators(region(), extracondition="1 limit 1")[0]

    def g(self, s=None, t=None, n=None, num=None, id=None):
        """
        TESTS::

            sage: from yacop.resolutions.minres import GFR
            sage: C=GFR(SteenrodAlgebra(3),memory=True)
            sage: C.extend(s=6,n=30)
            sage: g = C.g(s=5,n=0)
            sage: C.g(id=g["id"]) == g
            True
            sage: g.pop("id")  # random
            37
            sage: sorted(g.iteritems())
            [('e', 5), ('n', 0), ('num', 0), ('s', 5), ('t', 5)]
            sage: C.g(s=5,t=28)
            Traceback (most recent call last):
            ...
            ValueError: more than one generator in that region
            sage: C.g(s=5,t=28,num=1) # random
            {'e': 4, 'id': 53, 'n': 23, 'num': 1, 's': 5, 't': 28}
        """
        extracondition = ""
        if not id is None:
            extracondition = "rowid=%d" % id
            reg = region()
        else:
            reg = region(s=s, n=n, t=t)
            if not num is None:
                extracondition = "basid=%d" % num
        # print reg,extracondition
        lst = self.generators(reg, extracondition)
        if len(lst) < 1:
            raise ValueError("no such generator")
        if len(lst) > 1:
            raise ValueError("more than one generator in that region")
        return lst[0]

    def diff(self, src, target=None, opdeg=None, ptsonly=False):
        """
        Get the differential of the generator *src*. The result is returned
        as a list of pairs *(algebra element, generator)*.

        The differential can be filtered through these optional parameters:

             :target:      filter by target generator
             :opdeg:       filter by degree of the algebra element
             :ptsonly:     return only `P_t^s` and Bocksteins

        Note that you can search for a specific `P_t^s` or `Q_k` by combining *opdeg* and *ptsonly*.
        """

        from sage.algebras.steenrod.steenrod_algebra import (
            SteenrodAlgebra_mod_two,
            SteenrodAlgebra_generic,
        )

        cond = "srcgen = %d" % src["id"]
        if not (target is None):
            cond += " and targen = %d" % target["id"]
        if not (opdeg is None):
            if self._viewtype == "even":
                opdeg *= 2
            cond += " and opideg = %d" % opdeg
        funcname = "sagepoly_" + self._viewtype
        if ptsonly:
            funcname += "_PtsOnly"
        res = self.tcl.eval(
            r"""
               set result {}
               resolution db eval {
                   select %s(%d,group_concat(frag_decode(format,data),' '),targen) as spol from fragments
                   where %s group by targen, format
               } {
                  if {$spol ne ""} {
                     lappend result $spol
                  }
               }
               return "\[[join $result ,]\]"
            """
            % (funcname, self._prime, cond)
        )
        A = self._algebra
        # if self._viewtype == "odd":
        #    A = SteenrodAlgebra_generic(self._prime)
        # else:
        #    A = SteenrodAlgebra_mod_two()
        return eval(res)

    class GUI(Thread):
        def __init__(self, filename):
            Thread.__init__(self)
            self._filename = filename

        def run(self):
            from yacop.utils.tcl import tcl_interp, tcl_eval, loadTk

            tcl = tcl_interp()
            loadTk(tcl)
            tcl_eval(
                tcl,
                """
              set fname [lindex {%s} 0]
              yacop::sqlite db $fname
              set chv [yacop::chartgui db $fname]
              trace add variable [$chv forever] write "[list $chv destroy];#"
              vwait [$chv forever]
              update
           """
                % self._filename,
            )

    def gui(self):
        """
        Open a graphical user interface. This allows you to inspect the resolution, create
        postscript charts and to run SQL commands.
        """
        GFR.GUI(self._filename).start()

    def __sqlcon(self):
        """
        Open a SQL console to inspect the underlying database.
        """
        self.tcl.loadTk()
        self.tcl.eval("sqlconsole new [resolution db]")


class Subset(Parent, UniqueRepresentation):
    def __init__(self, minres, region):
        """
        The generators of the minimal resolution in a certain region.

        TESTS::

            sage: from yacop.resolutions.minres import GFR, Subset
            sage: from yacop.utils.region import region
            sage: C=GFR(SteenrodAlgebra(5))
            sage: S=Subset(C,region(tmax=20,smax=15)) ; S
            generators of minimal resolution of mod 5 Steenrod algebra, milnor basis in region(-Infinity < s <= 15, -Infinity < t <= 20)
            sage: S.category()
            Join of Category of finite enumerated sets and Category of yacop graded sets
            sage: TestSuite(S).run()
            sage: S=Subset(C,region(nmax=20)) ; S
            generators of minimal resolution of mod 5 Steenrod algebra, milnor basis in region(-Infinity < n <= 20)
            sage: S.category()
            Join of Category of infinite enumerated sets and Category of yacop graded sets
            sage: TestSuite(S).run()
            sage: TestSuite(S.an_element()).run()
        """
        self._res = minres
        self._reg = region
        if region.tmax < +Infinity or (
            region.smax < +Infinity and region.nmax < +Infinity
        ):
            cat = FiniteEnumeratedSets()
        else:
            # FIXME: finite sub hopf algebras with limited s are also finite
            cat = InfiniteEnumeratedSets()
        Parent.__init__(self, category=(cat, YacopGradedSets()))

    def _repr_(self):
        if not self._reg.is_full():
            return "generators of %s in %s" % (self._res, self._reg)
        else:
            return "generators of %s" % (self._res,)

    def an_element(self):
        it = iter(self)
        return next(it)

    def bbox(self):
        return self._reg.intersect(region(smin=0, tmin=0, emin=0))

    def _truncate_region(self, reg):
        return Subset(self._res, self._reg.intersect(reg))

    def degree(self, elem):
        dct = elem._dct
        return region(s=dct["s"], t=dct["t"], e=dct["e"], n=dct["n"])

    class walker(object):
        def __init__(self, owner):
            self.owner = owner
            self.id = -1

        def __iter__(self):
            return self.__class__(self.owner)

        def __next__(self):
            owner = self.owner
            id = self.id
            self.id += 1
            extendto = 0
            while True:
                elems = owner._res.generators(
                    owner._reg, extracondition=" rowid>%d order by rowid limit 1" % id
                )
                if len(elems) == 0:
                    if extendto < owner._reg.tmax or extendto < owner._reg.smax:
                        extendto += 5
                        owner._res.extend(region(smax=extendto, tmax=extendto))
                        continue
                    raise StopIteration
                assert len(elems) == 1
                return owner.element_class(owner, elems[0])

    def __iter__(self):
        if self in FiniteEnumeratedSets():
            self._res.extend(self._reg)
            return [
                self.element_class(self, d) for d in self._res.generators(self._reg)
            ].__iter__()
        return Subset.walker(self)

    def some_elements(self):
        it = iter(self)
        cnt = 0
        while cnt < 10:
            cnt += 1
            try:
                yield next(it)
            except StopIteration:
                break

    def __call__(self, x):
        try:
            assert self._res is x.parent()._res
            assert self._reg.contains(self.degree(x))
            return self.element_class(self, x._dct)
        except:
            raise

    def dump_element(self, el):
        return el._dct["id"]

    def load_element(self, el):
        return self.element_class(self, self._res.g(id=el))

    class Element(Element):
        def __init__(self, parent, dct):
            self._dct = dct
            Element.__init__(self, parent)
            self.n = dct["n"]
            # avoid conflicts with the inherited "n" method

        def _repr_(self):
            s, t, num = [self._dct[x] for x in ("s", "t", "num")]
            if num > 0:
                return "g(%d,%d,%d)" % (s, t, num)
            else:
                return "g(%d,%d)" % (s, t)

        def __getattr__(self, name):
            try:
                return self._dct[name]
            except:
                raise AttributeError

        def __eq__(a, b):
            return 0 == a.__cmp__(b)

        def __ne__(a, b):
            return not a.__eq__(b)

        def __cmp__(a, b):
            try:
                x = cmp(a.parent()._res, b.parent()._res)
            except:
                return -1
            if x != 0:
                return x
            try:
                return a._dct["id"].__cmp__(b._dct["id"])
            except:
                pass
            return -1

        def __richcmp__(a, b):
            return a.__cmp__(b)

        def __hash__(a):
            return a._dct["id"]


class MinimalResolution(FreeModuleImpl):
    """
    A minimal resolution of the Steenrod algebra or one of its subalgebras.

    EXAMPLES::

        sage: from yacop.resolutions.minres import MinimalResolution
        sage: A2 = SteenrodAlgebra(p=2,profile=(3,2,1,))
        sage: A2.rename("A(2)")
        sage: M = MinimalResolution(A2,memory=True) ; M
        minimal resolution of A(2)
        sage: B = M.free_basis() ; B
        generators of minimal resolution of A(2)

        sage: # create a quick ascii chart
        sage: dims = [[len(B.truncate(s=s,t=s+t)) for t in (0,..,20)] for s in reversed([0,..,15])]
        sage: print(matrix(dims).str(zero=' ',plus_one='*'))
        [*               *       *       *       *]
        [*               *       *       *       *]
        [*               *       *       *       *]
        [*               *       *       *       *]
        [*               *       *       *     * *]
        [*               *       *       *   * * *]
        [*               *       *       * *   * *]
        [*               *       *       * *     *]
        [*               *     * *       *       *]
        [*               *   * * *   *     *     *]
        [*               * *   * *   * *   * *   *]
        [*               * *     *   * *   * *   *]
        [*     *         *       *     *          ]
        [*   * *     *                            ]
        [* *   *                                  ]
        [*                                        ]

    TESTS::

        sage: TestSuite(M).run() # long time
    """

    @staticmethod
    def __classcall_private__(
        cls, algebra, memory=None, filename=None, category=None, istor=None
    ):
        if istor is None:
            istor = False
        return super(MinimalResolution, cls).__classcall__(
            cls,
            algebra,
            memory=memory,
            filename=filename,
            category=category,
            istor=istor,
        )

    def __init__(self, algebra, memory=None, filename=None, category=None, istor=False):
        """
        TESTS::

            sage: from yacop.resolutions.minres import MinimalResolution
            sage: A=SteenrodAlgebra(3)
            sage: M=MinimalResolution(A,memory=True) ; M
            minimal resolution of mod 3 Steenrod algebra, milnor basis
            sage: M.category()
            Category of yacop left modules over mod 3 Steenrod algebra, milnor basis
            sage: TestSuite(M).run()

        """
        self._worker = GFR(algebra, filename=filename, memory=memory)
        gens = Subset(self._worker, region())
        self._algebra = algebra
        self._filename = filename
        self._memory = memory
        self._istor = istor
        self._defcategory = category
        pro = ((), ()) if algebra.is_generic() else ()
        actalg = (
            SteenrodAlgebra(
                p=algebra.prime(), generic=algebra.is_generic(), profile=pro
            )
            if istor
            else algebra
        )
        if istor:
            actalg.rename("F%s" % algebra.prime())
        if category is None:
            category = YacopLeftModules(actalg)
            if istor:
                category = category.Subquotients()
        FreeModuleImpl.__init__(
            self, actalg, gens, None, True, False, category=category
        )

    def _repr_(self):
        return "minimal resolution of %s" % self._algebra

    def Chart(self):
        X = self._worker.Chart()
        X.rename("Chart of %s" % self)
        return X

    @cached_method
    def differential_morphism(self):
        """

        TESTS::

            sage: from yacop.resolutions.minres import MinimalResolution
            sage: A=SteenrodAlgebra(5)
            sage: M=MinimalResolution(A,memory=True) ; M
            minimal resolution of mod 5 Steenrod algebra, milnor basis
            sage: g = M.g(20,20)
            sage: d = M.differential
            sage: d(g)          # we should not really guarantee the coefficient here, but ...
            Q_0*g(19,19)
            sage: d(A.P(1)*g)   # we should not really guarantee the coefficient here, but ...
            Q_0 P(1)*g(19,19) + Q_1*g(19,19)
            sage: A=SteenrodAlgebra(2,generic=True,profile=((1,),(2,2)))
            sage: M=MinimalResolution(A,memory=True)
            sage: M.g(2,4).differential()
            P(1)*g(1,2)
            sage: sorted(M.g(2,6).differential())
            [(((0, 1), ()) g(1,2), 1), (((1,), (1,)) g(1,1), 1)]

        """
        return self.left_linear_morphism(
            codomain=self, on_basis=lambda g: self._differential_on_basis(g)
        )

    def differential(self, x):
        return self.differential_morphism()(x)

    def _generator_from_dict(self, dct):
        ge = self._gens.element_class
        return self(ge(self._gens, dct))

    def _differential_on_basis(self, g):
        ge = self._generator_from_dict
        return self.sum(self.A(a) * ge(x) for (a, x) in self._worker.diff(g._dct))

    def g(self, s, t, idx=0):
        """
        Return the generator with given s, t and index. Raises an error if there is no such generator.

        TESTS::

            sage: from yacop.resolutions.minres import MinimalResolution
            sage: M = MinimalResolution(SteenrodAlgebra(2,profile=(2,1)),memory=True)
            sage: M.g(3,7)
            g(3,7)
            sage: M.g(3,7).differential()
            Sq(3)*g(2,4) + Sq(2,1)*g(2,2)
            sage: M.g(2,7)
            Traceback (most recent call last):
            ...
            ValueError: no such generator

        """
        list(self._gens.truncate(s=s, t=t))
        # this triggers the computation up to this bidegree
        dct = self._worker.g(s=s, t=t, num=idx)
        return self._generator_from_dict(dct)

    def variable_names(self):
        """

        TESTS::

            sage: from yacop.resolutions.minres import MinimalResolution
            sage: M = MinimalResolution(SteenrodAlgebra(2),memory=True)
            sage: M.inject_variables()
            Defining g
            sage: M.differential(g(3,6))
            Sq(1)*g(2,5) + Sq(2)*g(2,4) + Sq(4)*g(2,2)
        """
        return [
            "g",
        ]

    def gens(self):
        return [
            self.g,
        ]

    def gui(self):
        return self._worker.gui()

    def _dump_term(self, el):
        return self.dump_element(self.monomial(el))

    def _load_term(self, el):
        return list(self.load_element(el)._monomial_coefficients)[0]

    class Element(FreeModuleImpl.Element):
        pass


class GeneratorSpace(MinimalResolution):
    @staticmethod
    def __classcall_private__(cls, algebra, memory=None, filename=None, category=None):
        return super(GeneratorSpace, cls).__classcall__(
            cls, algebra, memory=memory, filename=filename, category=category
        )

    def __init__(self, algebra, memory=None, filename=None, category=None):
        """
        TESTS::

            sage: from yacop.resolutions.minres import GeneratorSpace
            sage: A=SteenrodAlgebra(2,profile=(3,2,1))
            sage: A.rename("A")
            sage: T=GeneratorSpace(A,memory=True) ; T
            generator space of minimal resolution of A
            sage: T.category()
            Category of subquotients of yacop left modules over F2
            sage: TestSuite(T).run()
        """
        MinimalResolution.__init__(
            self,
            algebra,
            memory=memory,
            filename=filename,
            category=category,
            istor=True,
        )

    def _repr_(self):
        return "generator space of minimal resolution of %s" % self._algebra

    @cached_method
    def ambient(self):
        return MinimalResolution(
            self._algebra,
            filename=self._filename,
            memory=self._memory,
            category=self._defcategory,
        )

    def lift(self, el):
        return self.ambient()._from_dict(dict(el))

    def retract(self, el):
        aug = self._algebra.counit
        return self._from_dict(dict((k, aug(cf)) for (k, cf) in el))

    class Element(MinimalResolution.Element):
        pass


# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

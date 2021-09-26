r"""
Free modules over the Steenrod algebra.

    Fix pickling doc tests::

        sage: import __main__
        sage: from yacop.modules.free_modules import *
        sage: __main__.FreeModuleImpl = FreeModuleImpl
        sage: __main__.FreeModuleBasis = FreeModuleBasis
        sage: __main__.FreeModuleBasis_Element = FreeModuleBasis_Element

   TESTS at the prime 2::

      sage: A = SteenrodAlgebra(2) ; A.rename("A")
      sage: A1 = SteenrodAlgebra(2,profile=(2,1)) ; A1.rename("A(1)")
      sage: F = YacopFreeModule(A,('g','h'),right_action=True,left_action=True) ; F
      free module over A on [g, h]
      sage: F.category()
      Category of Yacop bimodules over A
      sage: TestSuite(F).run()
      sage: F.inject_variables()
      Defining g, h
      sage: gb = [Sq(0,1)*g, Sq(3)*g, Sq(0,1)*h, Sq(3)*h, Sq(1,1)*g, Sq(4)*g, Sq(1,1)*h, Sq(4)*h]
      sage: set(F.graded_basis(region(tmin=3,tmax=4))) == set(gb)
      True
      sage: G = YacopFreeModule(A,('x'),subalgebra=A1,tdegree=lambda x:2) ; G
      free module over (A//A(1)) on [x]
      sage: G.category()
      Category of yacop left modules over A
      sage: TestSuite(G).run()
      sage: G.inject_variables()
      Defining x
      sage: Sq(4)*x, Sq(2)*x
      (Sq(4)*x, 0)

   TESTS at odd primes::

      sage: A = SteenrodAlgebra(5) ; A.rename("A5")
      sage: A1 = SteenrodAlgebra(5,profile=((1,),(2,2))) ; A1.rename("A5(1)")
      sage: degs = { 'g' : (3,1,2), 'h' : (-1,2,0) }
      sage: F = YacopFreeModule(A,('g','h'),tesfunc = lambda g : degs[g]) ; F
      free module over A5 on [g, h]
      sage: F.category()
      Category of yacop left modules over A5
      sage: sorted(F.graded_basis(region(tmax=9)))
      [h, P(1)*h, Q_0*h, Q_0 P(1)*h, Q_0 Q_1*h, Q_1*h, g, Q_0*g]
      sage: sorted(F.graded_basis(region(tmax=13,emax=2)))
      [h, P(1)*h, g, P(1)*g, Q_0*g, Q_0 P(1)*g, Q_1*g]
      sage: F.an_element()
      2*h + 3*Q_0*h
      sage: TestSuite(F).run()
      sage: G = YacopFreeModule(A,('g'),tesfunc = lambda g : degs[g],subalgebra=A1) ; G
      free module over (A5//A5(1)) on [g]
      sage: G.category()
      Category of yacop left modules over A5
      sage: sorted(G.graded_basis(region(tmax=60)))
      [g, P(0,1)*g, P(5)*g, Q_2*g]
      sage: sorted(G.graded_basis(region(tmax=80,emax=1)))
      [g, P(0,1)*g, P(5)*g]
      sage: G.inject_variables()
      Defining g
      sage: G.an_element() == 2*g + 3*A.P(5)*g
      True
      sage: TestSuite(G).run()

      sage: # make sure pretty much anything is accepted as generator
      sage: x,y = var("x,y")
      sage: F = YacopFreeModule(A,(x,y)) ; F
      free module over A5 on [x, y]
      sage: F(x)
      x
      sage: A.P(0,1)*F(x)
      P(0,1)*x

    TESTS::

        sage: # build a presentation P -> Q -> C over A(2)
        sage: A = SteenrodAlgebra(2,profile=(3,2,1))
        sage: P = YacopFreeModule(A,(1,7,10),tdegree = lambda x:x)
        sage: Q = YacopFreeModule(A,('a',), tdegree = lambda x:0)
        sage: Q.inject_variables()
        Defining a
        sage: Sq(7)*a # check that Sq(7) acts, even though it's parent is not A
        Sq(7)*a
        sage: f = P.left_linear_morphism(codomain=Q, on_basis = lambda x : Sq(1)*a if x==1 else Sq(7)*a if x==7 else (Sq(4,2)+Sq(0,1,1))*a)
        sage: [(_,f(_)) for _ in P.gens()]
        [(1, Sq(1)*a), (7, Sq(7)*a), (10, Sq(0,1,1)*a + Sq(4,2)*a)]
        sage: C = f.cokernel()
        sage: len(C.graded_basis(tmax=50))
        17


"""


#*****************************************************************************
#       Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#  Distributed under the terms of the GNU General Public License (GPL)
#*****************************************************************************

from yacop.utils.region import region
from yacop.utils.gradings import YacopGrading
from yacop.utils.finite_graded_set import FiniteGradedSet
from yacop.modules.module_base import SteenrodModuleBase
from yacop.categories import YacopBiModules, YacopLeftModules, YacopRightModules, YacopGradedSets, YacopGradedObjects
from yacop.categories.functors import suspension, SuspendedObjectsCategory
from yacop.categories.functors import truncation, TruncatedObjectsCategory
from sage.rings.infinity import Infinity
#from sage.combinat.free_module import CombinatorialFreeModule
from sage.structure.sage_object import SageObject
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.sets.set import Set
from sage.sets.finite_enumerated_set import FiniteEnumeratedSet
from sage.sets.family import LazyFamily, Family
from sage.categories.examples.infinite_enumerated_sets import NonNegativeIntegers
from sage.categories.all import AlgebrasWithBasis
from sage.sets.integer_range import IntegerRange
from sage.algebras.all import SteenrodAlgebra, Sq
from sage.rings.integer import Integer
from sage.structure.formal_sum import FormalSum, FormalSums
from sage.structure.unique_representation import UniqueRepresentation
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.categories.infinite_enumerated_sets import InfiniteEnumeratedSets
from sage.structure.parent import Parent
from sage.structure.element import Element
from sage.misc.classcall_metaclass import ClasscallMetaclass
from yacop.utils.finite_graded_set import InfiniteGradedSet

class FreeModuleBasis(Parent,UniqueRepresentation):
    """
    A FreeModuleBasis enumerates the basis elements of a sum of shifted A//Bs.
    The generators can have an excess limit which allows to model unstable
    modules.

    TESTS::

       sage: from yacop.utils.finite_graded_set import FiniteGradedSet
       sage: from yacop.modules.free_modules import *
       sage: gens = FiniteGradedSet(('i',),tesfunc=lambda n:(1,1,3))
       sage: A=SteenrodAlgebra(2)
       sage: B=SteenrodAlgebra(2,profile=(3,2,1))
       sage: A.rename("A")
       sage: B.rename("A(2)")
       sage: X = FreeModuleBasis(A,gens,B) ; X
       basis of a free module over A//A(2) with generators [i]
       sage: Y = FreeModuleBasis(B,gens) ; Y
       basis of a free module over A(2) with generators [i]
       sage: Z = FreeModuleBasis(A,gens) ; Z
       basis of a free module over A with generators [i]
       sage: X.an_element()
       () i
       sage: X(gens.an_element()) == X.an_element()
       True
       sage: X.bbox()
       region(1 <= e < +Infinity, s = 3, 1 <= t < +Infinity)
       sage: Y.bbox()
       region(e = 1, s = 3, 1 <= t <= 24)
       sage: sorted(X.truncate(region(t=16)))
       [(0, 0, 0, 1) i]
       sage: sorted(Y.truncate(t=16))
       [(2, 2, 1) i, (5, 1, 1) i, (6, 3) i]
       sage: sorted(Z.truncate(t=16))
       [(0, 0, 0, 1) i, (0, 5) i, (1, 0, 2) i, (2, 2, 1) i, (3, 4) i, (5, 1, 1) i, (6, 3) i, (8, 0, 1) i, (9, 2) i, (12, 1) i, (15,) i]
       sage: sorted(Z.truncate(region(tmax=3)))
       [() i, (1,) i, (2,) i]
       sage: from itertools import islice
       sage: sorted(list(islice(Z.nontrivial_degrees(region(tmax=3)),100)))
       [region(e = 1, s = 3, t = 1), region(e = 1, s = 3, t = 2), region(e = 1, s = 3, t = 3)]
       sage: X.category()
       Join of Category of infinite enumerated sets and Category of yacop graded sets
       sage: TestSuite(X).run()
       sage: TestSuite(Y).run()
       sage: TestSuite(Z).run()

       sage: # test a free module with an infinite basis
       sage: I=FreeModuleBasis(A,X)
       sage: TestSuite(I).run()

    """

    @staticmethod
    def __classcall_private__(cls,algebra,gens,subalgebra=None,unstable=None,bbox=None,facade=None):
        if unstable is None:
            unstable = False
        if bbox is None:
            bbox = region()
        return super(FreeModuleBasis,cls).__classcall__(cls,algebra,gens,subalgebra,unstable,bbox,facade)

    def __init__(self,algebra,gens,subalgebra,unstable,bbox,facade):
        self._algebra = algebra
        self._unstable = unstable
        self._amil = algebra.an_element().change_basis('milnor').parent()
        self._subalg = subalgebra
        self._prime = self._algebra.characteristic()
        self._emask = 0
        self._trunc = bbox
        self._rmask = []
        if facade is None:
            print("WARNING: you should supply a reasonable facade")
            facade = self
        if subalgebra is not None:
           assert subalgebra._truncation_type == 0  ;# FIXME
           if not algebra.is_generic():
              e,r = (), subalgebra._profile
           else:
              r,e = subalgebra._profile
           msk=1
           for i in e:
              if 2==i:
                 self._emask = self._emask | msk
              msk = msk << 1
           self._rmask = r
        self._gens = gens
        if hasattr(gens,"dump_element"):
            self._dumpfuncs = gens.dump_element, gens.load_element
        else:
            import base64
            from sage.misc.persist import dumps, loads
            self._dumpfuncs = lambda x : base64.b64encode(dumps(x)), lambda x : loads(base64.b64decode(x))
        if self.is_finite():
            cat = FiniteEnumeratedSets()
            if not self._algebra.is_generic():
               emax = 0
            else:
               assert self._algebra._has_nontrivial_profile()
               rp,ep = self._profile
               emax = len(k for k in ep if k==2)
            self._algbox = region(tmin=0,tmax=self._algebra.top_class().degree(),emin=0,emax=emax,s=0)
        else:
            cat = InfiniteEnumeratedSets()
            self._algbox = region(tmin=0,emin=0,s=0)
        Parent.__init__(self, facade=facade, category=(cat,YacopGradedSets()))
        #self._set_grading(FreeModuleBasis.Grading(self))

    def gens(self):
       return self._gens

    def generator_names(self):
        return ["%s" % x for x in self._gens]

    def generators(self):
        one = self._algebra.one_basis()
        ec = self._make_element
        return [ec(one,g) for g in self._gens]

    def dump_element(self,el):
        enc,dec = self._dumpfuncs
        a,g = el.split()
        return str((a,enc(g)))

    def load_element(self,str):
        enc,dec = self._dumpfuncs
        a,e = eval(str)
        return self.element_class(self,a,dec(e))

    def _repr_(self):
       if self._subalg is None:
          xxx = "%s" % self._algebra
       else:
          xxx = "%s//%s" % (self._algebra,self._subalg)
       if self._trunc != region():
           yyy = "truncation to %s of " % self._trunc
       else:
           yyy = ""
       return "%sbasis of a free module over %s with generators %s" % (yyy, xxx, self.gens())

    def dim_min(self):
       return max(self.bbox().tmin,self._trunc.tmin)

    def dim_max(self):
       if not self.is_finite():
          return +Infinity
       adim = self._algebra.top_class().degree()
       if self._prime == 2:
          adim = 2*adim
       ans = adim + self._gens.bbox().tmax
       if self._trunc.tmax < Infinity:
           ans = min(self._trunc.tmax,ans)
       return Integer(ans)

    def is_finite(self):
        return (self._algebra.is_finite() or self._trunc.tmax < Infinity) and self._gens.is_finite()

    def an_element(self):
       one = self._algebra.one_basis()
       return self._make_element(one,self._gens.an_element())

    def some_elements(self):
       from itertools import islice
       return list(islice(self,10))

    def __call__(self,elem):
        try:
            a,g = elem._a, elem._g
            other = self._make_element(a,g)
            if other == elem:
                return other
        except:
            pass
        if elem in self._gens:
            one = self._algebra.one_basis()
            return self._make_element(one,elem)
        raise ValueError("%s not in %s" % (elem,self._gens))

    def _make_element(self,a,b):
       return self.element_class(self,a,b)

    def __iter__(self,reg=None):
       if reg is None:
          reg = region()
       tmin,tmax = reg.trange
       if tmin>tmax: return iter([])
       from itertools import chain
       mi,ma = self.dim_min(),self.dim_max()
       mi = max(mi,tmin)
       ma = min(ma,tmax)
       if mi > -Infinity: mi = Integer(mi)
       if ma < +Infinity: ma = Integer(ma+1)
       return chain.from_iterable(self._basis_in_dim(n,reg) for n in IntegerRange(mi,ma))

    def _region_iterator(self,reg):
       class walker(object):
          def __init__(self,other,region=None):
             self.o=other
             self.r=region
             self.it = self.o.__iter__(reg)
          def __iter__(self):
             return walker(self.o,self.r)
          def __next__(self):
             return next(self.it)
       return walker(self,reg)

    def _is_signature_allowed(self,key):
        if not self._algebra.is_generic():
            rc = self._basis_elem_ok((),key)
        else:
            e,r = key
            rc = self._basis_elem_ok(e,r)
        return rc

    def _basis_elem_ok(self,e,r):
       p = self._prime
       A = self._algebra
       cnt = 1
       for x in r:
          l = A.profile(cnt,0)
          if l==Infinity:
             break
          if x >= p**l:
             return False
          cnt = cnt+1
       for x in e:
          if A.profile(x,1)<2:
              return False
       for (x,y) in zip(r,self._rmask):
          if x % (p**y) != 0:
              return False
       for k in e:
          if self._emask & (1<<k):
              return False
       return True

    def _amodb_basis(self,n):
       # FIXME: this is currently slow and stupid
       from sage.algebras.steenrod.steenrod_algebra_bases import steenrod_algebra_basis
       p = self._prime
       generic = self._algebra.is_generic()
       if n<0: return
       for a in steenrod_algebra_basis(n,p=p,generic=generic):
          if not generic:
             e,r = (),a
          else:
             e,r = a
          if not self._basis_elem_ok(e,r):
             continue
          yield a

    def _basis_in_dim(self,n,reg=None):
       A = self._algebra
       G = self._gens
       def walk_basis():
          for g in G.truncate(tmax=n):
              gdg = G.degree(g)
              if gdg.e > reg.emax or gdg.s < reg.smin or gdg.s > reg.smax:
                  continue
              if not A.is_generic() and gdg.e < reg.emin:
                  continue
              i,i2 = gdg.trange
              if i>n: continue
              for a in self._amodb_basis(n-i):
                  if A.is_generic():
                      ae,ar = a
                      agedeg = gdg.e + len(ae)
                      if agedeg < reg.emin or agedeg > reg.emax:
                          continue
                  yield self._make_element(a,g)
       return walk_basis()

    def bbox(self,reg=None):
        res = self._algbox + self._gens.bbox()
        return res.intersect(region(reg).intersect(self._trunc))

    def _truncate_region(self,reg):
        reg = region.intersect(self.bbox(),reg)
        tmin,tmax = reg.trange
        if tmax<Infinity:
            def tesfunc(x):
                dg = self.degree(x)
                return (dg.t,dg.e,dg.s)
            return FiniteGradedSet(list(self._region_iterator(reg)),tesfunc=tesfunc)
        return FreeModuleBasis(self._algebra,self._gens,self._subalg,self._unstable,
            self._trunc.intersect(reg),facade=self.facade_for())

    def degree(self,elem):
        a,g = elem._a, elem._g
        ae = self._amil.monomial(a)
        if not self._algebra.is_generic():
            e,r = (),a
            ideg = ae.degree()
        else:
            e,r = a
            ideg = ae.degree()
        areg = region(s=0,e=len(e),t=ideg)
        greg = self._gens.degree(g)
        tot = areg+greg
        #print "degree of %s = %s" % (elem,tot)
        return tot


class FreeModuleBasis_Element(Element):
   def __init__(self,par,a,g):
      Element.__init__(self,par)
      self._a, self._g = a,g

   def split(self):
      return (self._a,self._g)

   def _repr_(self):
      return "%s %s" % self.split()

   def __eq__(self,other):
      a,g = self._a, self._g
      try:
         b,h = other._a,other._g
         return (a==b) and (g==h)
      except:
         return False

   def __ne__(a,b):
      return not a.__eq__(b)

   def __cmp__(a,b):
        ans = cmp(a._g,b._g)
        if ans != 0:
           return -ans
        ans = cmp(a._a,b._a)
        if ans != 0:
           return ans
        return 0

   def __hash__(self):
      return hash(self._a) ^ hash(self._g)

FreeModuleBasis.Element = FreeModuleBasis_Element

class FreeModuleImpl(SteenrodModuleBase):
    """
    """

    @staticmethod
    def __classcall_private__(cls,algebra,gens,subalgebra=None,left_action=None,right_action=None):
        if left_action is None:
            left_action = True
        if right_action is None:
            right_action = False
        return super(FreeModuleImpl,cls).__classcall__(cls,algebra,gens,subalgebra,left_action,right_action)

    def __init__(self,algebra,gens,subalgebra,left_action,right_action,category=None):
        """
        Free module over A//B where A and B are subalgebras of the Steenrod algebra.
        The generators can have an extra \"excess\" which allows to model
        free unstable modules.
        """

        if subalgebra is None:
            if category is None:
                if left_action:
                    if right_action:
                        category = YacopBiModules(algebra)
                    else:
                        category = YacopLeftModules(algebra)
                else:
                    if right_action:
                        category = YacopRightModules(algebra)
                    else:
                        raise ValueError("neither left_action, nor right_action specified")

        else:
            if left_action:
                category = YacopLeftModules(algebra)
            else:
                raise NotImplementedError("left quotient (B\\\\A) not implemented")

        self.A = algebra
        self.B = subalgebra
        self._left_action = left_action
        self.Am = algebra.an_element().change_basis('milnor').parent()
        self._gens = gens
        b = FreeModuleBasis(algebra,gens,subalgebra,facade=self)
        SteenrodModuleBase.__init__(self, b, category=category)

    def __call__(self,elem):
        try:
            return super(FreeModuleImpl,self).__call__(elem)
        except:
            try:
                # elem could come from a truncation or suspension of self._gens
                try:
                    elem = self._gens(elem)
                except:
                    pass
                return self.monomial(list(self.basis().keys())(elem))
            except:
                raise

    def _repr_(self):
        if self.B is None:
            return "free module over %s on %s" % (self.A, self._gens)
        return "free module over (%s//%s) on %s" % (self.A,self.B,self._gens)

    def _repr_term(self,elem):
        miln,gen = elem.split()
        a = self.Am.monomial(miln).change_basis(self.A.basis_name())
        if a == self.Am.one():
            return "%s" % gen
        if self._left_action:
            return "%s*%s" % (a,gen)
        else:
            return "%s*%s" % (gen,a)

    def left_linear_morphism(self,codomain=None,on_basis=None):
        """
        Create an A-linear map::

            sage: from yacop.modules.free_modules import YacopFreeModule
            sage: A = SteenrodAlgebra(3)
            sage: F.<a,b> = YacopFreeModule(A,('a','b'))
            sage: G.<g,h> = YacopFreeModule(A,('g','h'))
            sage: P,Q = A.P,A.Q_exp
            sage: f = F.left_linear_morphism(codomain=G,on_basis = lambda x : P(3)*g if x == 'a' else P(2)*h+Q(0,1)*g) ; f
            Generic morphism:
              From: free module over mod 3 Steenrod algebra, milnor basis on [a, b]
              To:   free module over mod 3 Steenrod algebra, milnor basis on [g, h]
            sage: f(a)
            P(3)*g
            sage: f(b)
            P(2)*h + Q_1*g
            sage: f(P(1)*a)
            P(4)*g
        """
        assert codomain is not None
        basmap = lambda x : self.A.monomial(x._a)*on_basis(x._g)
        return self.module_morphism(codomain=codomain,on_basis=basmap)

    def right_linear_morphism(self,codomain=None,on_basis=None):
        """
        Create an A-linear map::

            sage: from yacop.modules.free_modules import YacopFreeModule
            sage: A = SteenrodAlgebra(3)
            sage: F.<a,b> = YacopFreeModule(A,('a','b'),left_action=False,right_action=True)
            sage: G.<g,h> = YacopFreeModule(A,('g','h'),left_action=False,right_action=True)
            sage: P,Q = A.P,A.Q_exp
            sage: f = F.right_linear_morphism(codomain=G,on_basis = lambda x : g*P(3) if x == 'a' else h*P(2)+g*Q(0,1)) ; f
            Generic morphism:
              From: free module over mod 3 Steenrod algebra, milnor basis on [a, b]
              To:   free module over mod 3 Steenrod algebra, milnor basis on [g, h]
            sage: f(a)
            g*P(3)
            sage: f(b)
            h*P(2) + g*Q_1
            sage: f(a*P(1))
            g*P(0,1) + g*P(4)
        """
        assert codomain is not None
        basmap = lambda x : on_basis(x._g)*self.A.monomial(x._a)
        return self.module_morphism(codomain=codomain,on_basis=basmap)

    def _latex_term(self,elem):
        miln,gen = elem.split()
        a = self.Am.monomial(miln).change_basis(self.A.basis_name())
        if self._left_action:
            return "%s\\cdot %s" % (a,gen)
        else:
            return "%\\cdot %s" % (gen,a)

    def one(self):
        return self.monomial(0)

    def variable_names(self):
        return tuple(self.indices().generator_names())

    def gens(self):
        # doesn't work for infinite basis sets
        return tuple([self.monomial(g) for g in self.indices().generators()])

    def __getitem__(self,x):
        """
        Shortcut to access the "free_basis". This function is used when
        you access an Ext group like this::

            sage: import yacop
            sage: C=SteenrodAlgebra(2).resolution()
            sage: # access uses the coordinates (s,n)
            sage: print(C[2,8]) 
            [g(2,10)]
            sage: # rectangular (s,n)-ranges are also supported
            sage: print(sorted(C[2:4,8:10]))
            [g(2,10), g(3,11), g(3,12), g(4,13)]

        Note: with PEP 472 we could enhance indexing with more arguments.
        """
        if not isinstance(x,tuple) or len(x) != 2:
            raise ValueError("index not understood: %s" % x)
        dct = {}
        for (l,v) in zip(('s','n'),x):
            if isinstance(v,slice):
                a,b = v.start, v.stop
                if not v.step is None:
                    raise ValueError("stride slices not supported")
                mi = min(a,b)
                ma = max(a,b)
            else:
                idx = int(v)
                mi, ma = idx, idx
            dct["%smin"%l] = mi
            dct["%smax"%l] = ma
        return list(self(_) for _ in self.free_basis(**dct))

    def free_basis(self,**kwds):
        return self._gens.truncate(region(**kwds))

    def product_on_basis(self,left,right):
        raise NotImplementedError

    def left_steenrod_action_milnor(self,a,m):
        #print a, " * ", m
        miln,gen = m.split()
        b = self.Am.monomial(miln)
        a = self.Am.monomial(a)
        ec = self.indices()._make_element
        ans = []
        for (key,cf) in (a*b).monomial_coefficients().items():
            if self.indices()._is_signature_allowed(key):
                ans.append( (self.monomial(ec(key,gen)), cf) )
        return self.linear_combination(ans)

    def right_steenrod_action_milnor(self,m,a):
        #print a, " * ", m
        assert(self.B is None) # left quotients not implemented yet
        miln,gen = m.split()
        b = self.Am.monomial(miln)
        a = self.Am.monomial(a)
        ec = self.indices()._make_element
        ans = []
        for (key,cf) in (b*a).monomial_coefficients().items():
            ans.append( (self.monomial(ec(key,gen)), cf) )
        return self.linear_combination(ans)

    def dump_element(self,el):
        bas = list(self.basis().keys())
        dct = dict(el)
        return "%s" % [(bas.dump_element(k),dct[k]) for k in sorted(dct) if dct[k] != 0]

    def load_element(self,str):
        bas = list(self.basis().keys())
        return self._from_dict(dict([(bas.load_element(k),cf) for (k,cf) in eval(str)]))

    class Element(SteenrodModuleBase.Element):
        pass

def YacopFreeModule(algebra,gens,left_action=True,right_action=False,names=None,*args,**kwargs):
   """
   Free module over the Steenrod algebra.

   EXAMPLES::

      sage: from yacop.utils.region import region
      sage: from yacop.modules.free_modules import YacopFreeModule
      sage: A = SteenrodAlgebra(2) ; A.rename("A")
      sage: A1 = SteenrodAlgebra(2,profile=(2,1)) ; A1.rename("A(1)")
      sage: F = YacopFreeModule(A,('g','h')) ; F
      free module over A on [g, h]
      sage: sorted(F.graded_basis(region(tmax=3)))
      [h, Sq(0,1)*h, Sq(1)*h, Sq(2)*h, Sq(3)*h, g, Sq(0,1)*g, Sq(1)*g, Sq(2)*g, Sq(3)*g]
      sage: G = YacopFreeModule(A,('x'),subalgebra=A1,tdegree=lambda x:2) ; G
      free module over (A//A(1)) on [x]
      sage: sorted(G.graded_basis(region(tmax=12)))
      [x, Sq(0,0,1)*x, Sq(0,2)*x, Sq(4)*x, Sq(4,2)*x, Sq(8)*x]
   """
   subalg = kwargs.pop('subalgebra',None)
   gens = FiniteGradedSet(gens,*args,**kwargs)
   return FreeModuleImpl(algebra,gens,left_action=left_action,right_action=right_action,subalgebra=subalg)

# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

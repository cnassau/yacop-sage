r"""
Smash product resolutions

AUTHORS: - Christian Nassau (2011-05-13: version 1.0)

CLASS DOCUMENTATION:

TESTS::

    sage: import yacop
    sage: import __main__
    sage: __main__.rescount = 0
    sage: def newres(A):
    ....:    # return a fresh in-memory resolution for the algebra A
    ....:    from __main__ import rescount
    ....:    rescount = rescount+1
    ....:    return A.resolution(filename="file:testres%d?mode=memory" % rescount) 
    sage: __main__.newres = newres
    sage: C=newres(SteenrodAlgebra(2))

"""

#*****************************************************************************
#       Copyright (C) 2011-2018 Christian Nassau <nassau@nullhomotopie.de>
#  Distributed under the terms of the GNU General Public License (GPL)
#*****************************************************************************

from Tkynter import Tcl, TclError
from yacop.utils.tcl import Yacop
from yacop.utils.region import region
from sage.structure.element import Element
from yacop.modules.categories import YacopLeftModules, YacopGradedSets
from threading import Thread
from yacop.modules.free_modules import FreeModuleImpl
from yacop.resolutions.minres import GFR, MinimalResolution, Subset
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.rings.integer import Integer
from sage.rings.infinity import Infinity
from yacop.modules.functors import suspension
from sage.misc.cachefunc import cached_method
from sage.combinat.free_module import CombinatorialFreeModule
from sage.categories.category import Category
from sage.categories.vector_spaces import VectorSpaces
from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra
from copy import copy


# internal function for testing
def __newres(A,shared=False):
    global __rescount
    try:
        __rescount = __rescount+1
    except:
        __rescount = 0
    fname = "file:testres%d?mode=memory" % __rescount
    if shared: fname += "&cache=shared"
    return A.resolution(filename=fname) 

"""
    pickling doctest hack::

        sage: import __main__
        sage: from yacop.resolutions.smashres import *
        sage: __main__.Smasher = Smasher
        sage: __main__.SmashResolution = SmashResolution
"""

def tclsteenrodop(algebra,str):
    """
    Convert tcl string representation of a milnor basis element into Sage form.

    TESTS::

        sage: from yacop.resolutions.smashres import tclsteenrodop
        sage: A=SteenrodAlgebra(2)
        sage: tclsteenrodop(A,"{1 0 8 9}")
        Sq(8)
        sage: tclsteenrodop(A,"{1 0 {0 2} 9}")
        Sq(0,2)
        sage: EA=SteenrodAlgebra(2,generic=True)
        sage: tclsteenrodop(EA,"{1 6 {1 0} 9}")
        Q_1 Q_2 P(1,0)
        sage: A=SteenrodAlgebra(7)
        sage: tclsteenrodop(A,"{3 8 {2 0  1} 9}")
        3 Q_3 P(2,0,1)
        sage: tclsteenrodop(A,"{1 2 {} 0} {2 1 1 0}")
        2 Q_0 P(1) + Q_1
    """
    import string
    dct = {}
    for smd in str.split("} {"):
        op = smd.split(" ")
        op.pop()
        op = [string.atoi(u) for u in [x.strip("{").rstrip("}") for x in op] if u != '']
        cf = op[0]
        r = tuple(op[2::])
        if algebra.is_generic():
            e = tuple(idx for (idx,bit) in enumerate(Integer(op[1]).digits(2)) if bit == 1)
            dct[(e,r)] = cf
        else:
            dct[r] = cf
    return algebra._from_dict(dct)

class Smasher(Parent,UniqueRepresentation):
    """
    Object that represents `M\\otimes_A C_\\ast` for a
    minimal resolution `C_\\ast` and a differential right `A`-module `M`.
    """

    _memdbcnt = 0

    @staticmethod
    def __classcall_private__(cls,resolution,module,filename=None,debug=False):
        if filename is None:
            # create a unique URI filename
            Smasher._memdbcnt += 1
            import time
            filename = "file::yacopsr%d.%f?mode=memory&cache=shared" % (Smasher._memdbcnt, time.time())
            tempdb = True
        else:
            filename = 'file:' + os.path.join(Yacop.data_dir(),filename)
            tempdb = False
        return super(Smasher,cls).__classcall__(cls,resolution,module,filename,tempdb,debug)

    def __init__(self,resolution,module,filename=":memory:",tempdb=False,debug=False):

        import os
        if os.getenv('YACOP_FORCE_PRIVATE_CACHE') == 'Y':
            # used for parallel doctesting to avoid conflicts
            # between doctest processes
            filename = filename.replace('cache=shared','cache=private') 

        self.reference_resolution = resolution
        resolution = resolution._worker
        
        if not isinstance(resolution,GFR):
            raise ValueError, "first argument is not a resolution"

        self._resolution = resolution
        self._viewtype = resolution._viewtype
        self._module = module
        self._filename = filename
        self._tempdb = tempdb
        self._prime = self._resolution._prime
        self._errorhandler = None
        self.tcl = Yacop.Interpreter()

        modbbox = module.bbox()
        self._msmin = modbbox.smin
        self._mtmin = modbbox.tmin
        self._memin = modbbox.emin
        if self._msmin is -Infinity:
            raise ValueError, "module not bounded from below: smin=%s" % self._msmin
        if self._mtmin is -Infinity:
            raise ValueError, "module not bounded from below: tmin=%s" % self._mtmin
        if self._memin is -Infinity:
            raise ValueError, "module not bounded from below: emin=%s" % self._memin

        if self._viewtype == "even":
            self._tfactor = 2
        else:
            self._tfactor = 1

        # link the resolution into our Tcl interpreter
        self._resip = resolution.tcl.eval("namespace current")
        self.tcl.createcommand("sagemod",self._tclmodule)
        self.tcl.createcommand("errorCallback",self._errorcallback)

        spolyfunc = "sagepoly_%s" % resolution._viewtype

        self.tcl.eval("""
           yacop::smashres create smashprod {%s::resolution} {%s} [namespace current]::sagemod [namespace current]::errorCallback {%s}
           smashprod setDebug %s
           proc smashprod_fragment_iterator query {
               yield "start"
               set q [subst {
                   select
                   pydict('s',sg.sdeg,'i',sg.ideg,'e',sg.edeg, 
                   'srcrgen',sg.resgen, 'srcmod', m.sagename, 
                   'data', %s(%d,group_concat(frag_decode(f.format, f.data), ' ')), 
                   'tarmod', tm.sagename, 'tarrgen', tg.resgen) as p
                   from smash_generators sg 
                   join module_generators m on m.rowid = sg.modgen
                   join smash_fragments f on f.srcgen = sg.rowid
                   join smash_generators tg on tg.rowid = f.targen
                   join module_generators tm on tm.rowid = tg.modgen
                    $query 
                    group by f.srcgen, f.targen
                    order by sg.ideg-sg.sdeg, sg.edeg, sg.sdeg
               }]
               smashprod db eval $q {
                   yield $p
               }
           }
           """ % (self._resip, self._module, self._filename, debug, spolyfunc, resolution._prime))

    def filename(self):
        if self._tempdb:
            return None
        else:
            return self._filename

    def Chart(self,viewtype=None):
        from yacop.resolutions.charter import Charter
        if viewtype is None:
            viewtype = self._viewtype
        return Charter(self._filename, viewtype)

    def _errorcallback(self, location, message):
        if self._errorlocation is None:
            self._errorlocation = eval(location)
        self._errors.append(message)

    def _tclmodule(self,action,*args):
        """
        This funtion is a wrapper that is invoked from the Tcl code. 
        Its purpose is to provide access to the module.
        """
        #print action,args
        import string
        if action == 'actR':
            try:
                algebra = self._resolution._algebra
                el = self._module.load_element(args[0])
                op = tclsteenrodop(algebra,args[1])
                res = op % el
                ans = ""
                if not res.is_zero():
                    reg = region(s=res.s,t=res.t,e=res.e)
                    gb = self._module.graded_basis(reg)
                    cfs = self._module.graded_basis_coefficients(res,reg)
                    for (bel,cf) in zip(gb,cfs):
                        ans += " %d {%s}" % (cf,self._module.dump_element(bel))
                #print "actR",args,"=",res,"=",ans,"aus",op,"%",el
                return ans
            except Exception as e:
                print(e)
                raise e
        elif action == 'generators':
            algebra = self._resolution._algebra
            fac = self._tfactor ;# 1 if algebra.is_generic() else 2
            x = args[0].split(" ")
            reg = region(dict(zip(x[::2],(string.atoi(u) for u in x[1::2]))))
            #r2 = region(smax=reg.smax,
            #            tmax=(reg.smax+reg.nmax+(fac-1))/fac,
            #            emax=reg.emax)
            r2=reg
            r2.tmin = fac*r2.tmin
            r2.tmax = fac*r2.tmax
            #print reg,r2,args
            res = ""
            B = self._module.graded_basis(r2)
            #print r2,list(B)
            #print "basis of %s in %s = %s" % (self._module,r2,B)
            if not B.is_finite():
                #print "b not finite",r2
                raise ValueError, "module not finite in region %s" % r2
            for g in B:
                res += " {name {%s} sdeg %d ideg %d edeg %d}" % (self._module.dump_element(g),g.s,fac*g.t,g.e)
            #print res
            return res
        elif action == 'diff':
            # FIXME
            return ""
        if action == 'init':
            return
        #print action
        raise TclError, "action %s not implemented" % action

    def _repr_(self):
        return "Smasher (%s) * (%s), filename='%s'" % (self._module, self._resolution, self._filename)

    def _latex_(self):
        return "\\text{%s}" % self._repr_()

    def _getnfromst(self,s,t):
        return t/self._tfactor - s
    
    def _gettfromsn(self,s,n):
        return self._tfactor * (s+n)

    def _tabledump(self,sql):
        """
        TESTS::

            sage: from yacop.resolutions.smashres import SmashResolution, __newres
            sage: from yacop.modules.projective_spaces import RealProjectiveSpace
            sage: S=SmashResolution(RealProjectiveSpace(),__newres(SteenrodAlgebra(2)))
            sage: S._worker._tabledump("select 1 as tom, 2 as dick, 3 as harry")
            |       tom |      dick |     harry |
            |         1 |         2 |         3 |

        """
        self.tcl.eval("smashprod tabledump {%s}" % sql)

    def _find_region(self,reg):
        """
        Normalize the arguments to the "extend" method. The user supplied region
        can use bounds on the variables s,t,e,n. The interpretation of n depends
        on the viewtype. We need to translate this into 
           - truncation bounds on the module. the truncated module must be finite.
           - completeness requirements for the resolution.

        TESTS::

            sage: from yacop.resolutions.smashres import SmashResolution, __newres
            sage: from yacop.utils.region import region
            sage: newres = __newres
            sage: C = newres(SteenrodAlgebra(2))
            sage: from yacop.modules.projective_spaces import RealProjectiveSpace
            sage: P = RealProjectiveSpace(botexp=0,topexp=0)
            sage: P.bbox()
            region(e = 0, s = 0, t = 0)
            sage: from yacop.modules.functors import suspension

            sage: R=SmashResolution(P,C) ; R = R._worker
            sage: R._find_region(region(n=30))
            Traceback (most recent call last):
            ...
            ValueError: no upper s-bound given
            sage: # smin is not required, since the resolution has smin=0
            sage: R._find_region(region(n=30,smax=3))
            (region(-Infinity < t <= 34), [(0, 34), (1, 33), (2, 32), (3, 31), (4, 30)])
            sage: R._find_region(region(t=30,smax=3))
            (region(-Infinity < t <= 30), [(0, 30), (1, 29), (2, 28), (3, 27), (4, 26)])
            sage: R._find_region(region(t=30,s=3))
            (region(-Infinity < t <= 30), [(2, 28), (3, 27), (4, 26)])
            sage: R._find_region(region(n=30,s=3))
            (region(-Infinity < t <= 34), [(2, 32), (3, 31), (4, 30)])

            sage: P = RealProjectiveSpace(botexp=2,topexp=20)
            sage: R=SmashResolution(P,C) ; R = R._worker
            sage: R._find_region(region(smin=5,smax=7,nmin=10,nmax=15))
            (region(-Infinity < t <= 23), [(4, 17), (5, 16), (6, 15), (7, 14), (8, 13)])

            sage: R._find_region(region(t=3)) ;# infer smax from t
            (region(-Infinity < t <= 3), [(0, 1), (1, 0), (2, -1), (3, -2)])

            sage: P = RealProjectiveSpace(botexp=0,topexp=0)
            sage: M=cartesian_product((suspension(P,s=3,t=-17), suspension(P,s=2,t=-12))) ; M.bbox()
            region(e = 0, 2 <= s <= 3, -17 <= t <= -12)
            sage: R=SmashResolution(M,C) ; R = R._worker
            sage: # the following computation requires 
            sage: R._find_region(region(nmin=100,nmax=110,smin=50,smax=52))
            (region(-Infinity < t <= 163),
             [(47, 133), (48, 132), (49, 131), (50, 130), (51, 129)])

            sage: # examples with odd viewtype
            sage: C = newres(SteenrodAlgebra(2,generic=True))
            sage: from yacop.modules.classifying_spaces import BZpGeneric
            sage: M = BZpGeneric(2)
            sage: R=SmashResolution(M,C) ; R = R._worker
            sage: R._find_region(region(n=4,s=17))
            (region(-Infinity < t <= 22), [(16, 6), (17, 5), (18, 4)])

        """
        reg = copy(reg)

        mbbox = self._module.bbox()
        msmin, msmax = mbbox.srange
        mtmin, mtmax = mbbox.trange
        mnmin, mnmax = mbbox.nrange

        if mtmin == -Infinity:
            raise ValueError, "module not bounded from below in the t-direction"

        if reg.tmax < +Infinity:
            # we can infer an s-bound from tmax and mtmin
            smaxfromtmax = reg.tmax - mtmin + 1
            reg = region.intersect(reg,region(smax=smaxfromtmax)) 

        if reg.smax == +Infinity:
            raise ValueError, "no upper s-bound given"
        
        if msmin == -Infinity:
            raise ValueError, "module not bounded from below in the s-direction"

        reg.smin = max(reg.smin,msmin) ;# we assume resolution.smin == 0

        xtmin, xtmax = reg.trange
        xnmin, xnmax = reg.nrange
        xtmin = max(reg.smin+xnmin-1,xtmin)
        xtmax = min(reg.smax+xnmax+1,xtmax)

        mtrunc = region(tmax=xtmax)

        ressmax = reg.smax - msmin +1
        ressmin = reg.smin - msmin -1
        resbounds = []
        for s in range(ressmin,ressmax+1):
            if s<0: continue
            resbounds.append( (s,xtmax-s-mtmin) )

        return mtrunc, resbounds            

    def _make_smash_basis(self, mtrunc, dbg=False):
        """
        update the database tables for the given truncation of the module.
        """
        self.tcl.eval("smashprod update_module {%s}" % mtrunc.as_tcl())

        self.tcl.eval("smashprod update_smash_boxes")

    def _make_smash_fragments(self, reg, dbg=False):
        """
        compute the differentials on the new generators
        """
        self.tcl.eval("smashprod activate_smash_generators {%s}" % reg.as_tcl())
        self.tcl.eval("smashprod update_smash_fragments")

    def _make_smash_homology(self, reg, dbg=False):
        """
        compute the homology in the prescribed region
        """
        self.tcl.eval("smashprod update_homology {%s} %d" % (reg.as_tcl(),self._tfactor))
        self.tcl.eval("smashprod update_homology_fragments")

    def extend(self,reg=None,quiet=True,dbg=False,**kwargs):
        """
        extend the smasher computation to the required region
        automatically extends the reference resolution as required
        """
        from yacop.utils.region import region
        from copy import copy, deepcopy
        reg = copy(reg)

        if reg is None:
            reg = region()
        reg = reg.intersect(region(kwargs))

        mtrunc, sranges = self._find_region(reg)
        if dbg: 
            print "reg",reg
            print "mtrunc",mtrunc
            print "sranges",sranges

        for (s,n) in sranges:
            self._resolution.extend(reg=region(s=s,n=n),quiet=quiet)

        self._errors = []
        self._errorlocation = None

        if quiet:
            self.tcl.eval("yacop::sectionizer quiet on")
        else:
            self.tcl.eval("yacop::sectionizer quiet off")

        self._make_smash_basis(mtrunc,dbg=dbg)

        self._make_smash_fragments(reg,dbg=dbg)

        self._make_smash_homology(reg, dbg=dbg)

        if not self._errorhandler is None and not self._errorlocation is None:
            self._errorhandler(self._errorlocation)
    
    class GUI(Thread):
        def __init__(self,filename):
            Thread.__init__(self)
            self._filename=filename
        def run(self):
            from yacop.utils.tcl import tcl_interp, tcl_eval, loadTk
            tcl = tcl_interp()
            loadTk(tcl)
            tcl_eval(tcl,"""
              set fname [lindex {%s} 0]
              yacop::sqlite db $fname
              proc ::chartbusycb args { after 100; return 0 }
              db busy ::chartbusycb
              set chv [yacop::chartgui db $fname]
              trace add variable [$chv forever] write "[list $chv destroy];#"
              vwait [$chv forever]
              update
           """ % self._filename)

    def gui(self):
        """
        Open a graphical user interface. This allows you to inspect the resolution, create
        postscript charts and to run SQL commands.
        """
        GFR.GUI(self._filename).start()

    def sqlcon(self):
        """
        Open a SQL console to inspect the underlying database.
        """
        self.tcl.loadTk()
        self.tcl.eval("sqlconsole new [smashprod db]")


    def _search_condition(self,s=None,n=None,i=None,e=None,nov=None):
        """
        Create a where clause from the input parameters
        """

        if self._resolution._viewtype == 'even':
            nexp = "(s.ideg/2-s.sdeg)"
        else:
            nexp = "(s.ideg-s.sdeg)"

        cond = ""
        if not s is None: cond += " and s.sdeg = %d" % s
        if not i is None: cond += " and s.ideg = %d" % i
        if not n is None: cond += " and %s = %d" % (nexp,n)
        if not e is None: cond += " and s.edeg = %d" % e
        if not nov is None: cond += " and (s.sdeg-s.edeg) = %d" % nov
        if cond != "": cond = "where " + cond[4:]
        return (cond,nexp)

    def homology(self,s=None,n=None,i=None,e=None,nov=None):
        """
        Return basis of the homology in a range of degrees
        """

        (cond,nexp) = self._search_condition(s=s,n=n,i=i,e=e,nov=nov)

        res = "[" + self.tcl.eval( """
               join [smashprod db eval {
                   select pydict('id',rowid,'s',s.sdeg,'i',s.ideg,'e',s.edeg,'n',%s,'num',s.basid,'enum',s.ebasid) from homology_generators as s %s
               }] ,
            """ % (nexp,cond) ) + "]"
        #print res
        return Set([FormalSumOfDict([(1,Generator(self,x))],parent=self._fsums) for x in eval(res)])

    def generators(self, region, extracondition=""):
        """
        This routine is used by Subset(SmashResolutionHomology) to implement the basis of Ext(M)

        #TODO: The code is copied over from minres and should be refactored
        """
        if self._resolution._viewtype == 'even':
            nexp = "(ideg/2-sdeg)"
        else:
            nexp = "(ideg-sdeg)"

        from Tkynter import TclError
        def cond(var,col,fac=1):
            res = ""
            mi,ma = region.min(var), region.max(var)
            if mi > -Infinity:
                res += " and %s >= %d" % (col,fac*mi)
            if ma < +Infinity:
                res += " and %s <= %d" % (col,fac*ma)
            return res
        c = ""
        c += cond('s','sdeg')
        c += cond('t','ideg')
        c += cond('n','ndeg')
        c += cond('e','edeg')
        c += cond('b','(sdeg-edeg)')
        if len(c) and len(extracondition):
            c += " and "
        c += extracondition;
        while c[:4] == " and": c = c[4:]
        if len(c) and c[:5] != "where": c = "where " + c
        code =  """
               join [smashprod db eval {
                   select pydict('id',rowid,'s',sdeg,'t',ideg,
                     'e',edeg,'n',%s,'num',basid) 
                     from homology_generators %s
               }] ,
        """ % (nexp, c)
        #print code
        try:
            res = "[" + self.tcl.eval(code) + "]"
        except TclError as e:
            raise TclError, "query failed: %s\n%s" % (c,e.message)
        return eval(res)


    def smash_basis(self,s=None,n=None,i=None,e=None,nov=None):
        """
        Return A-basis of the smash product in a range of degrees
        """

        (cond,nexp) = self._search_condition(s=s,n=n,i=i,e=e,nov=nov)

        res = "[" + self.tcl.eval( """
               join [smashprod db eval {
                   select pydict('modgen',''''||m.sagename||'''','resgen',s.resgen)
                   from smash_generators as s
                   join module_generators as m on m.rowid = s.modgen %s
               }] ,
            """ % (cond) ) + "]"
        from sage.sets.set import Set
        return Set([(self._module._make_element_(x["modgen"]),self._resolution.g(id=x["resgen"])) for x in eval(res)])

    def fragments(self,querycond="where 1"):
        """
        """
        cname = self.tcl.eval("return fragiter[incr ::fragitercnt]")
        cor = self.tcl.eval("coroutine %s smashprod_fragment_iterator {%s}" % (cname, querycond))
        A = self._resolution._algebra
        R = self.reference_resolution
        while True:
            ans = self.tcl.eval(cname)
            if len(ans):
                dct = eval(ans)
                sg = R._generator_from_dict(self._resolution.g(id=dct['srcrgen']))
                tg = R._generator_from_dict(self._resolution.g(id=dct['tarrgen']))
                sm = self._module.load_element(str(dct['srcmod']))
                tm = self._module.load_element(str(dct['tarmod']))
                yield (sg,sm,dct['data'],tg,tm)
            else:
                break
        # FIXME: this code leaks coroutines if the generator is not executed to the end

    def _unpack_vector(self,row,basis):
        """
        Create a cycle from coefficient vector and basis
        """

        res = []
        idx=-1
        for coeff in row:
            idx=idx+1
            if coeff != 0:
                x = basis[idx]
                res.append((coeff,(self._module._make_element_(x["modgen"]),self._resolution.g(id=x["resgen"]))))

        return FormalSum(res,parent=self._fsums)

    def _getmatrix(self,what,s=None,n=None,i=None,e=None,nov=None):
        """
        Return cycles in a range of degrees
        """

        (cond,nexp) = self._search_condition(s=s,n=n,i=i,e=e,nov=nov)

        res = "[" + self.tcl.eval( """
               join [smashprod db eval {
                   select '(' || pymatrix(%s) || ',' ||
                      (select '['
                           || group_concat(pydict('modgen',''''||m.sagename||'''',
                                                  'resgen',subsel.resgen))
                           || ']' from smash_generators as subsel
                           join module_generators as m on m.rowid = subsel.modgen
                       where s.sdeg = subsel.sdeg and s.ideg = subsel.ideg and s.edeg = subsel.edeg)
                   || ')'
                   from smash_boxes as s
                   %s
               }] ,
            """ % (what,cond) ) + "]"

        #print "res=", eval(res)
        mat = []
        for (matrix,basis) in eval(res):
            for row in matrix:
                mat.append( self._unpack_vector(row,basis) )
        return mat

    def cycles(self,s=None,n=None,i=None,e=None,nov=None):
        """
        Return cycles in a range of degrees
        """

        return self._getmatrix('cycles',s=s,n=n,i=i,e=e,nov=nov)

    def boundaries(self,s=None,n=None,i=None,e=None,nov=None):
        """
        Return boundaries in a range of degrees
        """

        return self._getmatrix('boundaries',s=s,n=n,i=i,e=e,nov=nov)

    def cycle(self,generator):
        """
        Return a representing cycle for a homology generator.
        """

        mat = self._getmatrix('homology',s=generator["s"],i=generator["i"],e=generator["e"])
        #print mat
        return mat[generator["enum"]]

    def g(self,s=None,n=None,num=None,id=None):
        """
        Construct a homology generator from id or sequence number
        """

        import sage
        (cond,nexp) = self._search_condition()

        if not id is None:
            cond = "where rowid = %d" % id
        else:
            cond = "where sdeg = %d and ideg = n2i(%d,%d) and basid = %d" % (s,s,n,num or 0)

        res = "[" + self.tcl.eval( """
               join [smashprod db eval {
                   select pydict('id',rowid,'s',s.sdeg,'i',s.ideg,'e',s.edeg,'n',%s,'num',s.basid,'enum',s.ebasid) from homology_generators as s %s
               }] ,
            """ % (nexp,cond) ) + "]"
        #print res
        return [FormalSumOfDict([(1,Generator(self,x))],parent=self._fsums) for x in eval(res)][0]


    def homology_class(self,cycle):
        """
        Express cycle in terms of homology generators
        """

        cmd = "unset -nocomplain hclvar; set hclvar {}"
        for (coeff,smashgen) in cycle:
            (modgen,resgen) = smashgen
            #print "cf=",coeff," mgen=",modgen," rgen=",resgen
            cmd = cmd + ";lappend hclvar %d {%s} %d" % (coeff,modgen,resgen["id"])


        res = self.tcl.eval("""
                     %s
                     #puts hv=$hclvar
                     smashprod sage_homology_class $hclvar
                     """ % cmd)
        #print eval(res)
        return FormalSum([(cf,self.g(id=gid)) for (cf,gid) in eval(res)],parent=self._fsums)

    def _makeSageModule(self,region):

        from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra_generic, SteenrodAlgebra_mod_two

        self.tcl.eval("""
           if {[info commands sagemod] eq ""} {
               set smashdb [smashprod db]
               yacop::sagemodule create sagemod [%s::resolution config] $smashdb
           }
           """ % self._resip)

        # find the module generators that are already in the database
        modgens = list(self._module.basis(region))
        script = "set mgens {}\n"
        for g in modgens:
            degs = self._module.degrees(g)
            script += "lappend mgens {{%s} {s %d i %d e %d}}\n" % (g,degs["s"],degs["i"],degs["e"])
        todo = self.tcl.eval("%s ; sagemod addModuleGens $mgens" % script)
        if self._resolution._viewtype == "odd":
            A = SteenrodAlgebra_generic(self._resolution._prime)
        else:
            A = SteenrodAlgebra_mod_two()
        #print todo
        todo = eval(todo)
        #print todo
        resp = "unset -nocomplain df;unset -nocomplain ar;array set df {};array set ar {};"
        for g in todo["diff"]:
            mg = modgens[g]
            resp += "set g {%s};set df($g) {};" %mg
            dg = self._module.diff(mg)
            for (cf,tg) in list(dg):
                resp += "lappend df($g) %d {%s}\n" % (cf,tg)
        atodo = todo["actR"]
        for g in atodo:
            mg = modgens[g]
            resp += "set g {%s};set ar($g) {};" % mg
            for (yop,sop) in atodo[g]:
                resp += "lappend ar($g) {%s} {" % (yop)
                rs = self._module.actR(mg,sop)
                for (cf,tg) in list(rs):
                    resp += "%d {%s} " % (cf,tg)
                resp += "}\n"

        #print resp
        self.tcl.eval("""
              %s
              #parray df
              #parray ar
              sagemod addDiff [array get df]
              sagemod addActionR [array get ar]
              unset df
              unset ar
              #puts [sagemod db eval {select * from sagemod_ops}]
              #puts [smashprod db eval {select * from smash_fragments}]
           """ % resp)

from yacop.modules.module_base import SteenrodModuleBase_Tensor

class SmashResolution(SteenrodModuleBase_Tensor,UniqueRepresentation):

    @staticmethod
    def __classcall_private__(cls,module,resolution,filename=None, category=None, with_worker=None, debug=False):
        if with_worker is None:
            with_worker = True
        return super(SmashResolution,cls).__classcall__(cls,module,resolution,
                    filename=filename,category=category,with_worker=with_worker,debug=debug)

    def __init__(self, module, resolution, filename=None, category=None, with_worker=True, debug=False):
        """
        
        For a right `A`-module `M` and a MinimalResolution `C` of `A`, the SmashResolution(M,C)
        is the tensorproduct over `A` of `M` and `C`. It carries a differential that computes
        Ext_A(M).
        
        TESTS::

            sage: from yacop.resolutions.minres import MinimalResolution
            sage: from yacop.resolutions.smashres import SmashResolution
            sage: from yacop.modules.classifying_spaces import BZp
            sage: from yacop.modules.categories import *
            sage: A=SteenrodAlgebra(3,profile=((1,),(2,2)))
            sage: D=BZp(3)
            sage: C=MinimalResolution(A,memory=True)
            sage: S=SmashResolution(D,C) ; S
            Smash product resolution:
              resolution = minimal resolution of sub-Hopf algebra of mod 3 Steenrod algebra, milnor basis, profile function ([1], [2, 2])
              module = mod 3 cohomology of the classifying space of ZZ/3ZZ
            sage: S in YacopLeftModules(A)
            True
            sage: S.category()
            Category of tensor products of left Yacop modules over sub-Hopf algebra of mod 3 Steenrod algebra, milnor basis, profile function ([1], [2, 2])
            sage: TestSuite(S).run()

        It is possible to create SmashResolutions without database backing. This is required, for example,
        if the module is not connective::

            sage: from yacop.modules.dual_steenrod_algebra import DualSteenrodAlgebra
            sage: X=SmashResolution(DualSteenrodAlgebra(3),C,with_worker=False)
            WARNING: tensor product not locally finite in the t-direction
            WARNING: tensor product not locally finite in the e-direction
            sage: X
            Smash product resolution:
              resolution = minimal resolution of sub-Hopf algebra of mod 3 Steenrod algebra, milnor basis, profile function ([1], [2, 2])
              module = dual Steenrod algebra at the prime 3

        """
        if not isinstance(resolution, MinimalResolution):
            raise ValueError, "second argument must be a MinimalResolution"
        if category is None:
            category = resolution.category().TensorProducts()
        SteenrodModuleBase_Tensor.__init__(self,(module,resolution),category=category)
        #FIXME: suspensions should all share the same Smasher object
        if with_worker:
            self._worker = Smasher(resolution,module,filename=filename,debug=debug)
            self._worker._errorhandler = self._errorhandler
        else:
            self._worker = None

        result = lambda x,y : self.monomial((x,y))
        result = self._sets[0]._module_morphism(result, position = 0, codomain = self)
        result = self._sets[1]._module_morphism(result, position = 1, codomain = self)
        self._tc = result

    @staticmethod
    def SuspendedObjectsFactory(module,*args,**kwopts):
        """

        TESTS::

            sage: from yacop import *
            sage: from yacop.resolutions.smashres import SmashResolution
            sage: from yacop.resolutions.minres import MinimalResolution
            sage: from yacop.modules.classifying_spaces import BZp
            sage: A=SteenrodAlgebra(3,profile=((1,),(2,2)))
            sage: D=BZp(3)
            sage: C=MinimalResolution(A,memory=True)
            sage: S=SmashResolution(D,C)
            sage: S.category()
            Category of tensor products of left Yacop modules over sub-Hopf algebra of mod 3 Steenrod algebra, milnor basis, profile function ([1], [2, 2])
            sage: X=suspension(S,t=4)
            sage: X is SmashResolution(suspension(D,t=4),C)
            True
            sage: X.category()
            Category of tensor products of left Yacop modules over sub-Hopf algebra of mod 3 Steenrod algebra, milnor basis, profile function ([1], [2, 2])
        """
        return SmashResolution(suspension(module._sets[0],*args,**kwopts), module._sets[1])

    def _repr_(self):
        """
        TESTS::

            sage: from yacop.resolutions.smashres import SmashResolution
            sage: from yacop.modules.all import RealProjectiveSpace
            sage: A=SteenrodAlgebra(2)
            sage: S=SmashResolution(RealProjectiveSpace(),A.resolution()) ; S
            Smash product resolution:
              resolution = minimal resolution of mod 2 Steenrod algebra, milnor basis
              module = mod 2 cohomology of real projective space P^{+Infinity}
            sage: S.resolution()
            minimal resolution of mod 2 Steenrod algebra, milnor basis
            sage: S.module()
            mod 2 cohomology of real projective space P^{+Infinity}
        """
        mod, res = self._sets
        fileinfo = ""
        if not self._worker is None and not self._worker.filename() is None:
            fileinfo = "\n  storage: %s" % self._worker.filename()
        return "Smash product resolution:\n  resolution = %s\n  module = %s%s" % (res, mod,fileinfo)

    def module(self):
        return self._sets[0]

    def resolution(self):
        return self._sets[1]

    def _latex_(self):
        mod, res = self._sets
        return "%s \\land %s" % (latex(res), latex(mod))

    def Chart(self,*args,**kwds):
        X = self._worker.Chart(*args,**kwds)
        X.rename("Chart of %s" % self);
        return X

    def _errorhandler(self,location):
        """
        """
        print "internal error:", location
        for msg in self._worker._errors:
            print msg
        self._check_smash_fragments(location)
        raise RuntimeError, "internal error: inconsistency detected"

    def _check_smash_fragments(self,location):
        """
        Verify the smash_fragments table that was created in the underlying db. 
        """
        s,i,e = [location[_] for _ in ('s','i','e')] 
        frags = self._worker.fragments(querycond = """
            where sg.sdeg in (%d,%d,%d) and sg.ideg = %d
        """ % (s+1,s,s-1,i))
        for (sg,sm,op,tg,tm) in frags:
            s = self.make_tensor(sm,sg)
            t = self.make_tensor(tm,tg)
            print "fragments: ",s, "->",op,"*",t
            print "  diff(src) =", self.differential(s)
            print "     op*dst =", op*t
            print "     d(%s) =" % sg, self.resolution().differential(sg)
            print ""

    def _dump_term(self,el):
        mkey,ckey = el
        ael,gen = ckey.split()
        G=self._sets[1]._gens
        return (ael,G.dump_element(gen),mkey)

    def _load_term(self,el):
        ael,gid,mkey = el
        C=self._sets[1]
        G=C._gens
        gen = G.load_element(gid)
        bk=C.basis().keys()
        return (mkey,bk.element_class(bk,ael,gen))

    def tensor_constructor(self,modules):
        if len(modules) == 2:
            return self._tc
        else:
            return lambda x:x

    def make_tensor(self,modelem,celem):
        return self._tc(modelem,celem)

    @cached_method
    def differential_morphism(self):
        """

        TESTS::

            sage: from yacop.resolutions.smashres import SmashResolution
            sage: from yacop.resolutions.minres import MinimalResolution
            sage: from yacop.modules.classifying_spaces import BZp
            sage: A=SteenrodAlgebra(5)
            sage: D=BZp(5)
            sage: C=MinimalResolution(A,memory=True)
            sage: S=SmashResolution(D,C) ; S
            Smash product resolution:
              resolution = minimal resolution of mod 5 Steenrod algebra, milnor basis
              module = mod 5 cohomology of the classifying space of ZZ/5ZZ
            sage: D.inject_variables()
            Defining y, x
            sage: d=C.differential; g=C.g(5,43); g, d(g)  # random (because we don't want to guarantee the choice of d(g) here)
            (g(5,43), 2*Q_0*g(4,42) + P(1)*g(4,35))
            sage: a=S.make_tensor(x**2,g) ; a
            x^2 # g(5,43)
            sage: S.differential(a) == S.make_tensor(x**2,d(g))
            True
            sage: A.P(2)*a  # random
            x^10 # g(5,43) + x^6 # 2*P(1)*g(5,43) + x^2 # P(2)*g(5,43)
            sage: S.differential(A.P(2)*a) == A.P(2) * S.differential(a)
            True

        """
        return self.module_morphism(codomain=self,on_basis=lambda g:self._differential_on_basis(g))

    def differential(self,x):
        return self.differential_morphism()(x)

    def _differential_on_basis(self,g):
        mkey,ckey = g
        M,C = self._sets
        return self._tc(M.monomial(mkey),C.differential(C.monomial(ckey)))

    def gui(self):
        return self._worker.gui()

    def algebra(self):
        return self._sets[1]._algebra

    def factors(self):
        return (self._sets[0],None)

    def compute(self,quiet=False,**kwargs):
        """
        TESTS::

            sage: from yacop.resolutions.smashres import SmashResolution
            sage: from yacop.resolutions.minres import MinimalResolution
            sage: from yacop.modules.classifying_spaces import BZp
            sage: A=SteenrodAlgebra(5)
            sage: D=BZp(5)
            sage: # use a fresh resolution for this test. it should be automatically extended
            sage: C=MinimalResolution(A,filename='file:newresolutionxxx?mode=memory')
            sage: S=SmashResolution(D,C)
            sage: S.compute(smax=20,nmax=80,quiet=True)
            sage: E=S.Homology()
            sage: sorted(list(E.free_basis(s=3,imax=10)))

        """
        if self._worker is None:
            raise ValueError, "Smash resolution does not have database backing"
        reg = region(kwargs)
        self._worker.extend(reg=reg,quiet=quiet)

    def Homology(self):
        """
        TESTS::

            sage: from yacop.modules.A2module import A2Module
            sage: from yacop.resolutions.smashres import SmashResolution
            sage: SmashResolution(A2Module(17),SteenrodAlgebra(2).resolution()).Homology()
            Ext(M) over mod 2 Steenrod algebra, milnor basis
              M = A2 as a module over the mod 2 Steenrod algebra, module structure #17
        """
        return SmashResolutionHomology(self)

    class SmashResolutionElement(SteenrodModuleBase_Tensor.Element):
        pass


class SmashResolutionHomology(FreeModuleImpl,UniqueRepresentation):

    """
    TESTS::

        sage: from yacop.modules.all import BZp
        sage: A=SteenrodAlgebra(5)
        sage: M=BZp(5)
        sage: E=A.Ext(M)
        sage: L=E.free_basis(smax=2,tmax=20)
        sage: sorted(list(E.free_basis(s=2,tmin=18,tmax=20)))
        [g(2,18), g(2,19), g(2,20), g(2,20,1)]
        sage: sorted(list(E.free_basis(s=3,tmin=40,tmax=45)))
        [g(3,41), g(3,41,1), g(3,42), g(3,42,1), g(3,44)]


    """

    def __init__(self,resolution,category=None):
        """

        TESTS::

            sage: A=SteenrodAlgebra(2)
            sage: from yacop.modules.projective_spaces import QuaternionicProjectiveSpace
            sage: E = A.Ext(QuaternionicProjectiveSpace()) ; E
            Ext(M) over mod 2 Steenrod algebra, milnor basis
              M = mod 2 cohomology of quaternionic projective space P^{+Infinity}
            sage: E.category()
            Category of subquotients of left Yacop modules over F2
            sage: E.ambient()
            Smash product resolution:
              resolution = minimal resolution of mod 2 Steenrod algebra, milnor basis
              module = mod 2 cohomology of quaternionic projective space P^{+Infinity}
            sage: E.compute(s=10,t=20,quiet=True)

        """
        self._res = resolution
        assert isinstance(self._res,SmashResolution)
        from yacop.resolutions.minres import Subset
        self._res._worker.rename(self._repr_())
        gens = Subset(self._res._worker,region())
        algebra = self._res.algebra()
        pro = ((),()) if algebra.is_generic() else ()
        actalg = SteenrodAlgebra(p=algebra.prime(),generic=algebra.is_generic(),profile=pro)
        actalg.rename("F%s" % algebra.prime())
        if category is None:
            category = YacopLeftModules(actalg).Subquotients()
        FreeModuleImpl.__init__(self,actalg,gens,None,True,False,category=category)

    def _repr_(self):
        M,N = self._res.factors()
        if N is None:
            return "Ext(M) over %s\n  M = %s" % (self._res.algebra(),M)
        else:
            return "Ext(M,N) over %s\n  M = %s\n  N = %s" % (self._res.algebra(),M,N)

    def ambient(self):
        return self._res

    def compute(self,quiet=False,**kwargs):
        return self.ambient().compute(quiet=quiet,**kwargs)

    def gui(self):
        return self._res.gui()

    def Chart(self,*args,**kwds):
        return self.ambient().Chart(*args,**kwds)

    @staticmethod
    def SuspendedObjectsFactory(module,*args,**kwopts):
        """

        TESTS::

            sage: from yacop import *
            sage: from yacop.modules.classifying_spaces import BZp
            sage: A=SteenrodAlgebra(7)
            sage: suspension(A.Ext(BZp(7)),t=3) is A.Ext(suspension(BZp(7),t=3))
            True
        """
        return SmashResolutionHomology(suspension(module._res,*args,**kwopts))

# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

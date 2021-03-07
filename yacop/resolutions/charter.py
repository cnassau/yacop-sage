r"""

Chart plotting for resolution datafiles

AUTHORS: - Christian Nassau

CLASS DOCUMENTATION:
"""

#*****************************************************************************
#       Copyright (C) 2017 Christian Nassau <nassau@nullhomotopie.de>
#  Distributed under the terms of the GNU General Public License (GPL)
#*****************************************************************************

#from Tkynter import Tcl
from yacop.utils.tcl import Yacop
from yacop.utils.region import region
from sage.structure.sage_object import SageObject
from sage.plot.graphics import Graphics
from sage.plot.line import line2d
from sage.plot.point import point2d
from sage.rings.infinity import Infinity
from sage.rings.real_double import RDF

class Charter(SageObject):
    
    def __init__(self,dbname,vtp):
        self.tcl = Yacop.Interpreter()
        self.filename = dbname
        self.lineinfo = {}
        # use globalsetvar with dummy variable to cope with possible whitespace in path name
        Yacop.main.globalsetvar("FNAME",dbname)
        self.tcl.eval("yacop::sqlite [set db [namespace current]::chartdb] $::FNAME")
        self.tcl.eval("""
        
            $db eval {
                create temporary view chart_crowdiness
                as select ndeg as n, max(dim) as dim
                    from (select sdeg,ndeg,count(*) as dim from chart_generators
                          group by sdeg,ndeg)
                group by ndeg
            }
        
            proc chartgens {condition} {
                variable db
                set sql "select rowid,sdeg,ndeg,edeg,basid,dim from chart_generators cg
                         join chart_crowdiness cc on cg.ndeg = cc.n"
                if {$condition ne ""} {
                   append sql " where " $condition
                }
                append sql " order by sdeg, ndeg, edeg, basid"
                #puts sql=$sql
                yield
                $db eval $sql {
                   yield "$rowid|$sdeg|$ndeg|$edeg|$basid|$dim"
                }
            }

            proc clear_ptsops {} {
                variable opwatch 
                unset -nocomplain opwatch
            }

            proc add_ptsop {p m name} {
                variable opwatch
                set deg [steenrod::mono degree $p $m]
                lappend opwatch($deg) $m $name  
            }
            
            proc ptsfilt {opdg poly} {
                variable opwatch
                if {![info exists opwatch($opdg)]} return
                set res {}
                steenrod::poly foreach $poly m {
                    foreach {mo name} $opwatch($opdg) {
                        #puts m=$m,mo=$mo
                        if {[steenrod::mono isabove $m $mo]
                            && [steenrod::mono isbelow $m $mo]} {
                            lappend res $name@[steenrod::mono coeff $m]
                        }
                    }
                }
                return [join $res ,]
            }

            $db function ptsfilt [namespace current]::ptsfilt

            proc chartlines {} {
                variable db
                variable opwatch
                set degs [array names opwatch]
                set sql "
                    select cf.targen as targen, cf.opideg as opideg , ptsfilt(cf.opideg,cf.data) as ptsinfo,cf.srcgen as srcgen
                    from chart_fragments as cf where
                    opideg in ([join [set degs] ,])
                "
                yield 
                $db eval $sql {
                    if {$ptsinfo ne ""} {
                        yield "$targen|$opideg|$ptsinfo|$srcgen"
                    }
                }
            }
        """)
        self.vtp = None
        if not vtp is None:
            self.viewtype(vtp)
        
    def viewtypes(self):
        ans = self.tcl.eval("$db eval {select name from chart_viewtypes}")
        return ans.split(" ")
        
    def viewtype(self,newtype=None):
        if newtype is None:
            return self.vtp
        self.vtp = newtype
        self.tcl.eval("""
           set newtype "%s"
           set code [$db onecolumn {select code from chart_viewtypes where name=$newtype}]
           if {$code eq ""} { error "no such viewtype '$newtype'" }
           $db eval { drop view if exists chart_generators }
           $db eval { drop view if exists chart_fragments }
           $db eval { drop view if exists chart_geninfo }
           $db eval $code
        """ % newtype)
    
    def add_line(self,pts,argdict):
        defaults = {'zorder':5,'rgbcolor':(0,0,0)}
        defaults.update(argdict)
        # turn pts into the monomial format for the steenrod tcl library 
        isgen = pts.parent().is_generic()
        self.p = pts.parent().prime()
        for x in list(pts.monomial_coefficients()):
            if isgen:
                q,p = x
            else:
                q,p = (),x
            Q = sum(1<<_ for _ in q)
            s = "1 %d {%s} 0" % (Q, " ".join([str(_) for _ in p]))
            self.lineinfo[s] = (pts,defaults)
        
    def chartgens(self,region=None):
        cond = []
        if not region is None:
            if region.smax<Infinity:
                cond.append("sdeg <= %d" % region.smax)
            if region.nmax<Infinity:
                cond.append("ndeg <= %d" % region.nmax)
            if region.emax<Infinity:
                cond.append("edeg <= %d" % region.emax)
            if region.smin>-Infinity:
                cond.append("sdeg >= %d" % region.smin)
            if region.nmin>-Infinity:
                cond.append("ndeg >= %d" % region.nmin)
            if region.emin>-Infinity:
                cond.append("edeg >= %d" % region.emin)
        c = " and ".join(cond)
        with self.tcl.coroutine("chartgens {%s}" %c) as cor:
            for x in cor:
                yield dict(list(zip(["id","s","n","e","num","crwd"],(int(_) for _ in x.split("|")))))
                
    def chartlines(self):
        self.tcl.eval("clear_ptsops")
        lines = list(self.lineinfo)
        for (n,k) in enumerate(lines):
            self.tcl.eval("add_ptsop %d {%s} %d" % (self.p, k, n))
        with self.tcl.coroutine("chartlines") as cor:
            for x in cor:
                z = dict(list(zip(["tar","opdeg","info","src"],x.split("|"))))
                for u in z["info"].split(","):
                    z["name"],z["cf"] = u.split("@")
                    if int(z["cf"]) != 0:
                        z["line"] = lines[int(z["name"])]
                        yield z
        
    def geninfo(self,id):
        x = self.tcl.eval("""
            $db eval { select rowid,sdeg,ndeg,edeg,basid,dim from chart_generators cg
                         join chart_crowdiness cc on cg.ndeg = cc.n where cg.rowid = %d }
        """ % id)
        return dict(list(zip(["id","s","n","e","num","crwd"],(int(_) for _ in x.split(" ")))))
    
    def get_coords(self,pt):
        crowdiness = pt["crwd"]
        if crowdiness == 1:
            return (pt["n"],pt["s"])
        offset = 0.4-0.8*pt["num"]/(crowdiness-1)
        offset /= 2.5 # not sure about the best choice
        return (RDF(pt["n"]+offset),RDF(pt["s"]-offset))
    
    def make_chart(self,region=None):
        G = Graphics()
        smin,smax,nmin,nmax = [],[],[],[]
        for d in self.chartgens(region):
            x,y = self.get_coords(d)
            G += point2d((x,y),zorder=10)
            smin.append(y)
            smax.append(y)
            nmin.append(x)
            nmax.append(x)
            smin = [min(smin),]
            smax = [max(smax),]
            nmin = [min(nmin),]
            nmax = [max(nmax),]
        for l in self.chartlines():
            try:
                pts,lineargs = self.lineinfo[l["line"]]
                x1,y1 = self.get_coords(self.geninfo(int(l["src"])))
                x2,y2 = self.get_coords(self.geninfo(int(l["tar"])))
                G += line2d([(x1,y1),(x2,y2)],**lineargs)
            except:
                print("line not understood:",l)
        off=0.5
        G.ymin(smin[0]-off)
        G.ymax(smax[0]+off)
        G.xmin(nmin[0]-off)
        G.xmax(nmax[0]+off)
        return G

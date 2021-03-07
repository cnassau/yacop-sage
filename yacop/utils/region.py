r"""
region objects

The region command implements rectangular regions in the coordinates `a,b,...,z`.

TESTS AND EXAMPLES::

    sage: from yacop.utils.region import region
    sage: ur, vr = region(umin=13), region(umax=13,vmax=17,z=3)
    sage: print(ur)
    region(13 <= u < +Infinity)
    sage: print(vr)
    region(-Infinity < u <= 13, -Infinity < v <= 17, z = 3)
    sage: print(sorted(vr.vars()))
    ['u', 'v', 'z']
    sage: ir = region.intersect(ur,vr)
    sage: print(ir)
    region(u = 13, -Infinity < v <= 17, z = 3)
    sage: ir.vrange
    (-Infinity, 17)
    sage: ir.arange
    (-Infinity, +Infinity)
    sage: region(omin=17,omax=19).orange
    (17, 19)
    sage: xr = region(u=13,vmax=17,z=3)
    sage: xr == ir
    True
    sage: region.contains(ur,xr)
    True
    sage: region.contains(xr,ur)
    False
    sage: ur.contains_point(u=11,v=17)
    False
    sage: ur.contains_point(u=18)
    True
    sage: ur.contains_point(l=18,p=12)
    False
    sage: region(t=4,smax=7).shift(t=7,e=3)
    region(t = 11)
    sage: region(t=3,smax=7,emin=3) + region(t=2,smax=13,emin=4,r=5)
    region(7 <= e < +Infinity, -Infinity < s <= 20, t = 5)
    sage: (region(t=3) + region(e=8)).is_full()
    True
    sage: region().is_full()
    True
    sage: region(jmax=9).is_full()
    False
    sage: sorted(region(t=3,smax=7,emin=3).as_dict().items())
    [('emin', 3), ('smax', 7), ('tmax', 3), ('tmin', 3)]
    sage: region.span(region(x=0,y=0,zmax=0), region(x=1,y=0,zmax=1))
    region(0 <= x <= 1, y = 0, -Infinity < z <= 1)
    sage: region.negative(region(jmax=9,h=6))
    region(h = -6, -9 <= j < +Infinity)
    sage: region(tmin=4,tmax=10,k=4,smax=8) % "ts" 
    ([4, -Infinity], [10, 8])
    sage: r = region(xmax=5,y=4)
    sage: r.zmax, r.xmin, r.ymax
    (+Infinity, -Infinity, 4)
    sage: r.max('z'), r.min('x'), r.max('y'), r.val('y')
    (+Infinity, -Infinity, 4, 4)
    sage: r.val('x')
    Traceback (most recent call last):
    ...
    ValueError: range has no fixed x-coordinate
    sage: r.x
    Traceback (most recent call last):
    ...
    ValueError: range has no fixed x-coordinate
    sage: r = region(tmax=7,u=3,vmin=-1,vmax=17) ; r
    region(-Infinity < t <= 7, u = 3, -1 <= v <= 17)
    sage: r.var_mult({'t':2,'r':0,'v':-1})
    region(-Infinity < t <= 14, u = 3, -17 <= v <= 1)

    sage: # make sure empty regions are treated correctly
    sage: r = region(tmin=5,tmax=10) 
    sage: r.intersect(region(tmax=4))
    empty region
    sage: r.var_mult({'t':-1})
    region(-10 <= t <= -5)
    sage: r.var_mult({'t':0})
    region(t = 0)
    sage: r = region(tmin=10,tmax=5) ; r
    empty region
    sage: r.var_mult({'t':-1})
    empty region
    sage: r.var_mult({'t':0})
    empty region
    sage: r + region(tmin=0,tmax=100) 
    empty region
    sage: r.intersect(region(tmax=0))
    empty region
    sage: r=region(umax=10,i=3,tmax=17,tmin=-5)
    sage: r.is_finite('u','i')
    False
    sage: r.is_finite('i','t')
    True
    sage: region(region(smax=7).as_dict())
    region(-Infinity < s <= 7)
    sage: region(region(smax=7))
    region(-Infinity < s <= 7)


CLASS DOCUMENTATION:
"""

#*****************************************************************************
#       Copyright (C) 2009-2018 Christian Nassau <nassau@nullhomotopie.de>
#  Distributed under the terms of the GNU General Public License (GPL)
#*****************************************************************************

from sage.rings.infinity import Infinity
from sage.structure.sage_object import SageObject
from sage.sets.integer_range import IntegerRange
from sage.structure.unique_representation import UniqueRepresentation
from sage.misc.classcall_metaclass import ClasscallMetaclass

class region(SageObject):
    """
    This class represents a rectangular region in some `R^n`.

    EXAMPLES::

        sage: from yacop.utils.region import region
        sage: region(tmin=-14, tmax=27, smin=11, l=23)
        region(l = 23, 11 <= s < +Infinity, -14 <= t <= 27)

    """

    @staticmethod
    def _normalize_vars(dct=None,**kwargs):
        kws = {}
        if dct is None:
            dct = {}
        for (k,v) in list(dct.items()):
            if len(k) == 1 or (len(k) == 4 and k[1:] in ["max","min"]):
                kws[k] = v
        for (k,v) in list(kwargs.items()):
            if len(k) == 1 or (len(k) == 4 and k[1:] in ["max","min"]):
                kws[k] = v
        for (k,v) in list(kws.items()):
            if v is None:
                del kws[k]
            if k[1:] == "min" and v == -Infinity:
                del kws[k]
            if k[1:] == "max" and v == +Infinity:
                del kws[k]
        return kws
        #return super(region,cls).__classcall__(cls,**kws)
       
    def __init__(self,dct=None,**kwargs):
        if isinstance(dct,region):
            dct = dct.as_dict()
        self._dct = {}
        for k,v in list(region._normalize_vars(dct=dct,**kwargs).items()):
            self.__setattr__(k,v)
   
    def _fmtrange(self,v1,v2,val,op1,op2):
        op = op1
        if val == Infinity or val == -Infinity:
           op = op2
        return "%s %s %s" % (v1,op,v2)
  
    def _getrange(self,var):
        dct = object.__getattribute__(self, '_dct')
        min = dct.get("%smin" % var,-Infinity)
        max = dct.get("%smax" % var,+Infinity)
        if min>max: min,max=+Infinity,-Infinity
        return min,max
        
    def _getdict(self):
        return object.__getattribute__(self, '_dct')

    def as_dict(self):
        return self._getdict()

    def as_tcl(self):
        return " ".join("%s %s" % (a,b) for (a,b) in self.as_dict().items())

    def __mod__(self,vars):
        d = [self._getrange(v) for v in vars]
        return [v[0] for v in d], [v[1] for v in d]

    def intersect(*regions):
        """
        Compute the intersection of regions::

           sage: from yacop.utils.region import region
           sage: region.intersect(region(x=3),region(ymin=7))
           region(x = 3, 7 <= y < +Infinity)
        """
        full = region()
        regs = [full if r is None else r for r in regions]
        vx = [r.vars() for r in regs]
        vars = set().union(*vx)
        r = {}
        for v in vars:
            mins = [rg._getrange(v)[0] for rg in regs]
            maxs = [rg._getrange(v)[1] for rg in regs]
            r["%smin" % v] = max(mins)
            r["%smax" % v] = min(maxs)
        return region(**r)

    def span(*regions):
        """
        Compute the span of regions::

           sage: from yacop.utils.region import region
           sage: region.span(region(x=3),region(x=7))
           region(3 <= x <= 7)
        """
        full = region()
        regs = [full if r is None else r for r in regions]
        vx = [r.vars() for r in regs]
        vars = set().union(*vx)
        r = {}
        for v in vars:
            mins = [rg._getrange(v)[0] for rg in regs]
            maxs = [rg._getrange(v)[1] for rg in regs]
            r["%smin" % v] = min(mins)
            r["%smax" % v] = max(maxs)
        return region(**r)

    def negative(r):
        kw = {}
        for v in r.vars():
            mi,ma = r._getrange(v)
            if mi<=ma: mi,ma = -ma,-mi
            kw["%smin" % v] = mi
            kw["%smax" % v] = ma
        return region(**kw)

    def __eq__(r1,r2):
        return 0 == r1.__cmp__(r2)
  
    def __ne__(r1,r2):
        return not r1.__eq__(r2)

    def __cmp__(r1,r2):
        for v in sorted(r1.vars().union(r2.vars())):
            x1 = r1.__getattribute__("%srange"%v)
            x2 = r2.__getattribute__("%srange"%v)
            for (a,b) in zip(x1,x2):
               if a != b:
                  return -1 if a<b else +1
        return 0

    def is_full(self):
        for v in self.vars():
            min,max = self._getrange(v)
            if (not min is -Infinity) or (not max is +Infinity):
                return False
        return True

    def contains(r1,r2):
        """
        Test if `r_1` is contained in `r_2`::

            sage: from yacop.utils.region import region
            sage: region(x=3).contains(region(x=3,emin=17))
            True
            sage: region(xmin=3).contains(region(x=2))
            False
        """
        return r2 == region.intersect(r1,r2)

    def contains_point(self,**kwargs):
        """
        Test if a "point" is contained in the region::

            sage: from yacop.utils.region import region
            sage: region(xmin=3,mmax=7).contains_point(x=3,z=8,m=5)
            True
        """
        return self.contains(region(**kwargs))

    def vars(self):
        """
        Return set of variables of the region::

            sage: from yacop.utils.region import region
            sage: sorted(region(imin=4,kmax=8).vars())
            ['i', 'k']
        """
        dct = self._getdict()
        return set(key[0] for key in dct)

    def shift(self,**kwargs):
        return region.__add__(self,region(**kwargs))

    def __add__(r1,r2):
        r = {}
        for v in r1.vars().union(r2.vars()):
            min1,max1 = r1._getrange(v)
            min2,max2 = r2._getrange(v)
            r["%smin" % v] = min1+min2
            r["%smax" % v] = max1+max2
        return region(**r)   

    def var_mult(self,dct):
        r = {}
        for v in self.vars():
            mi,ma = self._getrange(v)
            if mi<=ma and v in dct:
                mi = mi*dct[v]
                ma = ma*dct[v]
                mi,ma = min(mi,ma), max(mi,ma)
            r["%smin" % v] = mi
            r["%smax" % v] = ma
        return region(**r)

    def _repr_(self):
        dct = self._getdict()
        r = []
        for v in sorted(self.vars()):
            min,max = self._getrange(v)
            if min>max: return "empty region"
            if min == -Infinity and max == +Infinity:
               continue
            if min == max:
                r.append("%s = %s" % (v,min))
            else:
                smin = self._fmtrange(min,'',min,"<=","<")
                smax = self._fmtrange('',max,max,"<=","<")
                r.append("%s%s%s" % (smin,v,smax))
        return "region(%s)" % ", ".join(r)
   
    def is_empty(self):
        for v in sorted(self.vars()):
            min,max = self._getrange(v)
            if min>max: 
                return True
        return False

    def __hash__(self):
        return hash(self._repr_())

    def _is_range_attribute(self,name):
        x = name[1:]
        if x == "" or x == "max" or x == "min" or x == "range":
            return True
        return False
    
    def is_finite(self,*vars):
        assert len(vars)>=1 # answer for empty var list is unintuitive
        for var in vars:
            min,max = self._getrange(var)
            if min == -Infinity or max == +Infinity:
                return False
        return True

    def min(self,var):
        return self._getrange(var)[0]

    def max(self,var):
        return self._getrange(var)[1]

    def val(self,var):
        min,max = self._getrange(var)
        if min==max:
            return min
        raise ValueError("range has no fixed %s-coordinate" % var)

    def __getattribute__(self,nm):
        if not region._is_range_attribute(self,nm):
            return object.__getattribute__(self, nm)
        dct = object.__getattribute__(self, '_dct')
        if nm[1:] in ["range", "max", "min", ""]:
            min,max = self._getrange(nm[0])
            if min>max: min,max = +Infinity,-Infinity # try to normalize the empty region
            if nm[1:] == "range":
                return (min,max)
            elif nm[1:] == "max":
                return max
            elif nm[1:] == "min":
                return min
            if min==max:
                return min
            raise ValueError("range has no fixed %s-coordinate" % nm)
        val = None
        try:
            val = dct[nm]
        except KeyError:
            pass
        return val
        
    def __setattr__(self,nm,val):
        if not region._is_range_attribute(self,nm):
            return object.__setattr__(self,nm,val)
        dct = object.__getattribute__(self, '_dct')
        if nm[1:] == "":
            dct["%smax"%nm] = val
            dct["%smin"%nm] = val
        else:
            dct[nm] = val
        


# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

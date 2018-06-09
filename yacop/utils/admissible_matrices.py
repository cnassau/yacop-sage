r"""
Enumeration of admissible Milnor matrices

AUTHORS:

 - Christian Nassau (2018): initial revision

"""
#*****************************************************************************
#  Copyright (C) 2018      Christian Nassau <nassau@nullhomotopie.de>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************

from sage.matrix.constructor import matrix
from sage.structure.parent import Parent
from sage.structure.sage_object import SageObject
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.combinat.integer_vector_weighted import WeightedIntegerVectors
from yacop.utils.bitstuff import binom_modp
from sage.rings.integer_ring import ZZ

class AdmissibleMatrices(Parent):

    def __init__(self, prime, exponents, maxn=None):
        """
        TESTS::

            sage: from yacop.utils.admissible_matrices import AdmissibleMatrices
            sage: X = AdmissibleMatrices(3, (4,0,3)) ; X
            admissible matrices for prime 3, exponents [4, 0, 3]
            sage: for (cf,x,colsums,diagsums) in X:
            ....:    print("-- cf=%d, colsums=%s, diagsums=%s"%(cf,colsums,diagsums))
            ....:    print(x.str(zero='.'))
            -- cf=1, colsums=[1, 2], diagsums=[1, 1, 0, 1]
            [1 1]
            [. .]
            [. 1]
            -- cf=1, colsums=[4, 1], diagsums=[4, 0, 0, 1]
            [4 .]
            [. .]
            [. 1]
            -- cf=1, colsums=[4, 1], diagsums=[1, 1, 3, 0]
            [1 1]
            [. .]
            [3 .]
            -- cf=1, colsums=[7, 0], diagsums=[4, 0, 3, 0]
            [4 .]
            [. .]
            [3 .]

        """
        self.p = prime
        self.one = GF(self.p).one()
        self.exp = list(exponents)
        self.maxn = 99999 if maxn is None else maxn 
        me = max([0, ] + self.exp)
        self.powers = [1, ]
        pow = self.p
        i = 0
        while pow <= me:
            self.powers.append(pow)
            pow *= self.p
            i += 1
            if i>self.maxn:
                break
        self.ncols = len(self.powers)
        self.nrows = len(exponents)
        self.max = matrix(GF(self.p), self.nrows, self.ncols)
        for i in range(self.nrows):
            for j in range(self.ncols):
                self.max[i, j] = self.exp[i] // self.powers[j]
        Parent.__init__(self, category=FiniteEnumeratedSets())

    def _repr_(self):
        ans = "admissible matrices for prime %d, exponents %s" % (self.p, self.exp)
        if self.maxn < 99999:
            ans += ", limit %d" % self.maxn
        return ans

    def enumerate(self):
        """
        TESTS::

            sage: from yacop.utils.admissible_matrices import AdmissibleMatrices
            sage: X = AdmissibleMatrices(3, (17,5,9), maxn=3) ; X
            admissible matrices for prime 3, exponents [17, 5, 9], limit 3
            sage: for (cf,x,colsums,diagsums) in X:
            ....:    print("-- cf=%d, colsums=%s, diagsums=%s"%(cf,colsums,diagsums))
            ....:    print(x.str(zero='  '))
            -- cf=2, colsums=[19, 1, 1], diagsums=[8, 2, 11, 0, 0]
            [ 8     1]
            [ 2  1   ]
            [ 9      ]
            -- cf=1, colsums=[19, 4, 0], diagsums=[8, 5, 10, 0, 0]
            [ 8  3   ]
            [ 2  1   ]
            [ 9      ]
            -- cf=1, colsums=[28, 1, 0], diagsums=[17, 2, 10, 0, 0]
            [17      ]
            [ 2  1   ]
            [ 9      ]
            -- cf=1, colsums=[22, 0, 1], diagsums=[8, 5, 10, 0, 0]
            [ 8     1]
            [ 5      ]
            [ 9      ]
            -- cf=2, colsums=[22, 3, 0], diagsums=[8, 8, 9, 0, 0]
            [ 8  3   ]
            [ 5      ]
            [ 9      ]
            -- cf=1, colsums=[31, 0, 0], diagsums=[17, 5, 9, 0, 0]
            [17      ]
            [ 5      ]
            [ 9      ]

        """
        ans = matrix(ZZ, self.nrows, self.ncols)
        col = matrix(ZZ, self.nrows, self.ncols)
        dia = matrix(ZZ, self.nrows, self.ncols)
        for (cf,ans,col,dia) in self._enumerate_row(ans, col, dia, 0):
            cols, diags = list(col.row(0)), list(dia.row(0))
            for i in range(1,self.nrows):
                diags.append(dia[i,self.ncols-1])
            yield (cf,ans,cols,diags)


    def _enumerate_row(self,ans,col,dia,rownum):
        if rownum == self.nrows-1:
            loop = [(self.one,ans,col,dia),].__iter__()
        else:
            loop = self._enumerate_row(ans,col,dia,rownum+1)
        for (cf,a,c,d) in loop:
            # fill in row #rownum
            for sol in WeightedIntegerVectors(self.exp[rownum],self.powers):
                cf2 = cf
                isbad = False
                for (i,s) in enumerate(sol):
                    if s>0 and rownum+i>=self.maxn:
                        isbad = True
                        break
                    a[rownum,i] = s
                    if rownum+1<self.nrows:
                        cprev = c[rownum+1,i]
                        dprev = 0 if i==0 else d[rownum+1,i-1]
                    else:
                        cprev = 0
                        dprev = 0
                    c[rownum,i] = cprev + s
                    d[rownum,i] = dprev + s
                    cf2 *= binom_modp(self.p,dprev+s,s)
                    if cf2.is_zero():
                        isbad = True
                        break
                if isbad:
                    continue
                yield (cf2,a,c,d)

    def __iter__(self):
        return AdmissibleMatrices.Iterator(self)

    class Iterator:

        def __init__(self, admat):
            self.gen = admat.enumerate()

        def next(self):
            return self.gen.next()

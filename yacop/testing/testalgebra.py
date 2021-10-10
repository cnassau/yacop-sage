r"""
Helper classes for doctesting the SteenrodAlgebraBase class.
"""

#pylint: disable=E0213

from yacop.modules.algebra_base import SteenrodAlgebraBase
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.finite_rings.finite_field_constructor import FiniteField
from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra
from yacop.utils.region import region

class Testclass1(SteenrodAlgebraBase):
    """
    Implementation of "BZp * BZp"
    """

    def __init__(this,p,category=None):
        """
        TESTS::

            sage: from yacop.testing.testalgebra import Testclass1
            sage: X=Testclass1(5)
            sage: X.monomial((2,1,8,0))
            x^2*a*y^8
            sage: X.monomial((3,0,-17,1))
            x^3*b/y^17

            sage: from yacop.utils.region import region
            sage: X._manual_test_left_action(region(tmax=20))
            1126 non-zero multiplications checked
            sage: X._manual_test_left_conj_action(region(tmax=20)) # long time
            1148 non-zero multiplications checked

        """
        # must admit the "category" keyword for suspendability
        R = PolynomialRing(FiniteField(p),"x,a,y,b")
        x,a,y,b = R.gens()
        I = R.ideal([a**2,b**2])
        degs = lambda idx : (1,-1,0) if (idx&1) else (2,0,0)
        SteenrodAlgebraBase.__init__(this,R,[degs(n) for n in range(4)],I,
                                    SteenrodAlgebra(p),category=category)

    def _left_steenrod_coaction_milnor_gen(this,idx,maxq,maxp):
        """
        TESTS::

            sage: from yacop.testing.testalgebra import Testclass1
            sage: X=Testclass1(3)
            sage: X.inject_variables()
            Defining x, a, y, b

            sage: # the left coaction on the generators
            sage: list(X._left_coaction_on_basis((1,0,0,0), 3, ()))
            [(x)*1]
            sage: list(X._left_coaction_on_basis((0,1,0,0), 3, ()))
            [(a)*1, (x)*tau(1), (x^3)*tau(0,1)]
            sage: list(X._left_coaction_on_basis((0,0,1,0), 3, ()))
            [(y)*1]
            sage: list(X._left_coaction_on_basis((0,0,0,1), 3, ()))
            [(b)*1, (y)*tau(1), (y^3)*tau(0,1)]

            sage: # sign test for coproduct of a*b
            sage: sorted(list(X._left_coaction_on_basis((0,1,0,1), 1, ())))
            [(2*x*b)*tau(1), (a*b)*1, (a*y)*tau(1)]

            sage: # coaction on x and x^{-1}
            sage: sorted(list(X._left_coaction_on_basis((1,0,0,0), 0, (30,))))
            [(x)*1, (x^3)*xi(1)]
            sage: sorted(list(X._left_coaction_on_basis((2,0,0,0), 0, (30,))))
            [(2*x^4)*xi(1), (x^2)*1, (x^6)*xi(2)]
            sage: sorted(list(X._left_coaction_on_basis((3,0,0,0), 0, (30,))))
            [(x^3)*1, (x^9)*xi(3)]
            sage: sorted(list(X._left_coaction_on_basis((-1,0,0,0), 0, (13,))))
            [(1/x)*1,
            (2*x)*xi(1),
            (2*x^13)*xi(7),
            (2*x^17)*xi(9),
            (2*x^21)*xi(11),
            (2*x^25)*xi(13),
            (2*x^5)*xi(3),
            (2*x^9)*xi(5),
            (x^11)*xi(6),
            (x^15)*xi(8),
            (x^19)*xi(10),
            (x^23)*xi(12),
            (x^3)*xi(2),
            (x^7)*xi(4)]
            sage: sorted(list(X._left_coaction_on_basis((-5,0,0,0), 0, (5,))))
            [(1/x^3)*xi(1), (1/x^5)*1, (x)*xi(3), (x^3)*xi(4)]

        """
        from yacop.utils.bitstuff import Delta
        if 1&idx:
            # coact(a) = sum tau_k x^(p^k)
            yield this._coaction_tensor(this.gens()[idx],0,())
            for (i,digit) in zip(list(range(0,1000)),reversed(bin(maxq)[2:])):
                if digit=='1':
                    res = this.gens()[idx-1]**(this._prime**i)
                    yield this._coaction_tensor(res,1<<i,())
        else:
            # coact(x) = sum xi_k x^(p^k)
            for (i,exp) in zip(list(range(0,1000)),[1,]+list(maxp)):
                if exp>0:
                    res = this.gens()[idx]**(this._prime**i)
                    yield this._coaction_tensor(res,0,Delta(i))

    def _bbox(this):
        return region(tmin=0,s=0,emax=0)

    def _can_test_pickling(this):
        return False # pickling not implemented

r"""
Collection of utility functions related to binomials and multinomials

"""

#*****************************************************************************
#       Copyright (C) 2011 Christian Nassau <nassau@nullhomotopie.de>
#  Distributed under the terms of the GNU General Public License (GPL)
#*****************************************************************************

from sage.rings.infinity import Infinity
from sage.rings.integer import Integer
from sage.misc.cachefunc import cached_function
from sage.arith.all import binomial

    
@cached_function        
def _binomtable(prime,n,m):
   """
   cached values of binomial(n,m) for n in (0,..,prime-1)
   """
   assert (n<prime) and (0<=n)
   return binomial(n,m)

def binom_modp(p,n,m):
   """
   optimized computation of binomial(n,m) mod p

   EXAMPLE::

      sage: from yacop.utils.bitstuff import binom_modp
      sage: binom_modp(5,37,26)
      2
      sage: binomial(37,26)
      854992152
   """
   assert m>=0
   ans=1
   while m>0:
      ans *= _binomtable(p,n%p,m%p)
      n,m = n//p, m//p
   return ans%p

def bitcount(val):
    """
    Count number of ones in binary expansion of ``val``.

    TESTS::

       sage: from yacop.utils.bitstuff import bitcount
       sage: b=7
       sage: for u in (0,..,500):
       ...       if 3!=bitcount(b):
       ...          assert 0==1
       ...       b=b*2

    """
    res = 0
    assert val >= 0
    while val>0:
        i = val & 0xffffffff
        val = val >> 32
        i = i - ((i >> 1) & 0x55555555)
        i = (i & 0x33333333) + ((i >> 2) & 0x33333333)
        aux = (((i + (i >> 4) & 0xF0F0F0F) * 0x1010101) & 0xffffffff) >> 24
        res = res + aux
    return res

def sign_correction(a,b):
    """ 
    Compute the sign change between "a^b" and the exterior algebra multiplictation "a*b"

    TESTS::

        sage: from yacop.utils.bitstuff import sign_correction
        sage: sign_correction(1,2)
        0
        sage: sign_correction(2,1)
        1
        sage: sign_correction(1,-2)
        0
        sage: sign_correction(2,-3)
        1
        sage: sign_correction(-2,1)
        Traceback (most recent call last):
        ...
        AssertionError
    """
    assert a>=0
    if b<0:
        bc = -1-b
        msk=1
        while msk<=a or msk<=bc: msk = msk<<1
        b = b+ (msk<<1)
    assert b>=0
    res = 0
    cnt = 0
    while a: 
        x = a & (a-1)
        z = a ^ x
        cnt = cnt+1
        res = res + bitcount((z-1) & b)
        a = x
        b = b | z
    # implicitly we've had to reverse a, since it's easier to isolate the
    # lowest bit than the highest. Here we make up for the reversion: 
    res = res + ((2 & cnt) >> 1)
    return (1&res)

def Delta(idx):
    """
    Exponent sequence ``Delta_idx``

    TESTS::

        sage: from yacop.utils.bitstuff import Delta
        sage: Delta(0)
        ()
        sage: Delta(1)
        (1,)
        sage: Delta(4)
        (0, 0, 0, 1)
    """
    if idx<=0:
       return ()
    return tuple([0 for u in range(1,idx)] + [1,])

def qexp_to_bitmask(qexp):
    """
    Convert exponential Bockstein notation to bitmask.

    EXAMPLE::

       sage: from yacop.utils.bitstuff import qexp_to_bitmask
       sage: bin(qexp_to_bitmask((0,3,4)))
       '0b11001'
    """
    ans = 0
    for exp in qexp:
       ans = ans | (1<<exp)
    return ans

def N0():
    """
    infinite generator (0,1,2,...)
    """
    cnt=-1
    while True:
        cnt = cnt+1
        yield cnt
    

# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

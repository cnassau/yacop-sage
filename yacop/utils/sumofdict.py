r"""
Steenrod algebra ground field resolutions

AUTHORS: - Christian Nassau (2009-03-27: version 1.0)

This package allows to compute a minimal resolution of a sub 
Hopf-algebra of the Steenrod algebra. 

INTRODUCTION:

.. [SQLite] Project homepage `<http://www.sqlite.org>`_.


CLASS DOCUMENTATION:
"""

#*****************************************************************************
#       Copyright (C) 2009 Christian Nassau <nassau@nullhomotopie.de>
#  Distributed under the terms of the GNU General Public License (GPL)
#*****************************************************************************

from sage.structure.formal_sum import FormalSum, FormalSums

class FormalSumOfDict(FormalSum):
    """
    A FormalSum variant with an extra __getitem__ method
    """

    def __getitem__(self, key):
        res = None
        for (cf,gen) in list(self):
            if not res is None:
                if gen[key] != res:
                    raise KeyError("inconsistent entries for key %s" % key)
            else:
                res = gen[key]
        if res is None:
            raise KeyError("cannot determine '%s' because sum is zero" % key)
        return res






# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

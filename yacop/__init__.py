
__version__ = '2.0'

from yacop.utils.region import region
from yacop.utils.suspenders import Suspender

from yacop.categories.functors import suspension, truncation

def cokernel(f):
   """
   Construct the cokernel of the map ``f``.
   """
   return f.cokernel()

import yacop.utils
import yacop.utils.startup
yacop.utils.startup.__startup__()

# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

# development tools for the yacop package - not imported per default
from sage.repl.attach import attach
import yacop


def doattach(module):
    fname = module.__file__
    import os

    name, ext = os.path.splitext(fname)
    if ext == ".pyc":
        ext = ".py"
    attach(name + ext)


import yacop.utils.gradings

doattach(yacop.utils.gradings)
doattach(yacop.utils.region)
import yacop.utils.finite_graded_set

doattach(yacop.utils.finite_graded_set)
doattach(yacop.utils.set_of_elements)
import yacop.modules.module_base

doattach(yacop.modules.module_base)
doattach(yacop.modules.functors)
doattach(yacop.modules.categories)
import yacop.modules.free_modules

doattach(yacop.modules.free_modules)
import yacop.modules.algebras

doattach(yacop.modules.algebras)
import yacop.modules.dual_steenrod_algebra

doattach(yacop.modules.dual_steenrod_algebra)
import yacop.modules.projective_spaces

doattach(yacop.modules.projective_spaces)
import yacop.modules.classifying_spaces

doattach(yacop.modules.classifying_spaces)


def mro(M):
    print(("MRO ", M))
    for u in M.__class__.mro():
        print(("  ", u))


# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

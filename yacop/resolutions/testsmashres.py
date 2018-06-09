"""

TESTS::

    sage: # turn on a couple of extra diagnostic routines
    sage: import os
    sage: os.putenv('YACOP_DOUBLECHECK','1')

    sage: from yacop.modules.projective_spaces import *
    sage: from yacop.resolutions.smashres import SmashResolution, __newres
    sage: C=__newres(SteenrodAlgebra(2,profile=(1,)))
    sage: S=SmashResolution(ComplexProjectiveSpace(2),C)
    sage: S.compute(smin=3,smax=8,nmin=10,nmax=30,quiet=True)
    sage: # all generators are "I"dle since none of them lie in the computed region
    sage: S._worker._tabledump(("select resgen,modgen,sdeg,ideg,status" 
    ....:                        " from smash_generators"
    ....:                        " where sdeg<3 order by sdeg, ideg"))
    |    resgen |    modgen |      sdeg |      ideg |    status |
    |         1 |         1 |         0 |         4 |         I |
    |         1 |         2 |         0 |         8 |         I |
    |         2 |         1 |         1 |         6 |         I |
    |         2 |         2 |         1 |        10 |         I |
    |         3 |         1 |         2 |         8 |         I |
    |         3 |         2 |         2 |        12 |         I |
    sage: S.compute(smax=8,nmax=30,quiet=True)
    sage: # check that we have the fragments for the h0-multiplication
    sage: S._worker._tabledump(("select g.ideg, f.opideg,f.opedeg,"
    ....:                        " frag_decode(f.format,f.data) as data"
    ....:                        " from smash_fragments f join"
    ....:                        " smash_generators g on g.rowid = f.srcgen"
    ....:                        " where g.sdeg = 1 order by ideg"))
    |      ideg |    opideg |    opedeg |      data |
    |         6 |         2 |         0 | {1 0 1 0} |
    |        10 |         2 |         0 | {1 0 1 0} |
    sage: S.compute(smin=3,smax=7,nmin=0,nmax=10,quiet=True)


    sage: # compute an Ext chart in small non-contigous pieces
    sage: # there is a danger that the homology or the smash_fragments
    sage: # along the boundary of this computation get messed up
    sage: # make sure this is not the case
    sage: from yacop.modules.projective_spaces import *
    sage: from yacop.resolutions.smashres import SmashResolution, __newres
    sage: C=__newres(SteenrodAlgebra(2,profile=(1,)),shared=True)
    sage: S=SmashResolution(RealProjectiveSpace(),C)
    sage: E=S.Homology() ; E
    Ext(M) over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [1]
      M = mod 2 cohomology of real projective space P^{+Infinity}
    sage: # E should be zero for s>0 since RealProjectiveSpace() is free over A(0)
    sage: sql = ("select b.sdeg, b.ideg, b.edeg," 
    ....:        " count(*) as dim from homology_gendata h" 
    ....:        " join smash_boxes b on b.rowid=h.boxid" 
    ....:        " group by b.sdeg, b.ideg, b.edeg"
    ....:        " having dim>0"
    ....:        " order by b.sdeg, b.ideg, b.edeg")
    sage: E.compute(smin=5,smax=7,nmin=10,nmax=15,quiet=True)
    sage: S._worker._tabledump(sql) ;# no cohomology = no output 
    sage: E.compute(smin=2,smax=4,nmin=2,nmax=8,quiet=True)
    sage: S._worker._tabledump(sql) ;# no cohomology = no output 
    sage: E.compute(smin=3,smax=5,nmin=5,nmax=9,quiet=True)
    sage: S._worker._tabledump(sql) ;# no cohomology = no output 
    sage: E.compute(smin=4,smax=4,nmin=5,nmax=12,quiet=True)
    sage: S._worker._tabledump(sql) ;# no cohomology = no output 
    sage: sorted(list(E.free_basis(smax=14,nmax=10)))
    [g(0,1), g(0,3), g(0,5), g(0,7), g(0,9)]

    sage: # test that failed earlier
    sage: from yacop.modules.projective_spaces import *
    sage: from yacop.resolutions.smashres import SmashResolution, __newres
    sage: C=__newres(SteenrodAlgebra(2,profile=(2,1,)),shared=True)
    sage: S=SmashResolution(ComplexProjectiveSpace(),C)
    sage: E=S.Homology()
    sage: E.compute(s=0,nmin=3,nmax=6,quiet=True)

    sage: # do the same for complex projective space. earlier we
    sage: # saw some missing h0-multiplications in the homology chart
    sage: from yacop.modules.projective_spaces import *
    sage: from yacop.resolutions.smashres import SmashResolution, __newres
    sage: C=__newres(SteenrodAlgebra(2,profile=(2,1,)),shared=True)
    sage: S=SmashResolution(ComplexProjectiveSpace(),C)
    sage: E=S.Homology()
    sage: E.compute(smin=5,smax=7,nmin=10,nmax=15,quiet=True)
    sage: E.compute(smin=2,smax=4,nmin=2,nmax=8,quiet=True)
    sage: E.compute(smin=3,smax=5,nmin=5,nmax=9,quiet=True)
    sage: E.compute(smin=4,smax=4,nmin=5,nmax=12,quiet=True)
    sage: sorted(list(E.free_basis(smax=14,nmax=10)))
    sage: S._worker._tabledump(("select ideg from homology_generators g"
    ....:                        " left join homology_fragments f on f.srcgen = g.rowid"
    ....:                        " where g.sdeg = 2 and g.ideg <=24 and not f.format is null"
    ....:                        " order by g.ideg"))
    |      ideg |
    |         8 |
    |        12 |
    |        16 |
    |        20 |
    |        24 |

    sage: D=__newres(SteenrodAlgebra(2,profile=(2,1,)),shared=True)
    sage: F=SmashResolution(ComplexProjectiveSpace(),D)
    sage: F.compute(smax=5,nmax=20,quiet=True)
    sage: F._worker._tabledump(("select ideg from homology_generators g"
    ....:                        " left join homology_fragments f on f.srcgen = g.rowid"
    ....:                        " where g.sdeg = 2 and g.ideg <=24 and not f.format is null"
    ....:                        " order by g.ideg"))
    |      ideg |
    |         8 |
    |        12 |
    |        16 |
    |        20 |
    |        24 |

    sage: # check that an earlier sign problem is fixed
    sage: from yacop.resolutions.smashres import SmashResolution, __newres
    sage: from yacop.modules.classifying_spaces import BZp
    sage: from yacop.modules.functors import truncation
    sage: C=__newres(SteenrodAlgebra(5),shared=True)
    sage: E=SmashResolution(truncation(BZp(5),tmax=12),C)
    sage: E.compute(smax=3,nmax=30,quiet=True)

    sage: from yacop.resolutions.smashres import SmashResolution, __newres
    sage: from yacop.modules.classifying_spaces import BZp
    sage: C=__newres(SteenrodAlgebra(7),shared=True)
    sage: E=SmashResolution(BZp(7),C)
    sage: E.compute(smax=7,nmax=130,quiet=True)

    sage: from yacop.resolutions.smashres import SmashResolution, __newres
    sage: from yacop.modules.dickson import DicksonAlgebra
    sage: C=__newres(SteenrodAlgebra(2),shared=True)
    sage: E=SmashResolution(DicksonAlgebra(2,2),C)
    sage: E.compute(smax=3,nmax=5,quiet=True)

    sage: from yacop.resolutions.smashres import SmashResolution, __newres
    sage: from yacop.modules.dickson import DicksonAlgebra
    sage: C=__newres(SteenrodAlgebra(3),shared=True)
    sage: E=SmashResolution(DicksonAlgebra(3,2),C)
    sage: E.compute(smax=2,nmax=20,quiet=True)

    sage: from yacop.resolutions.smashres import SmashResolution, __newres
    sage: from yacop.modules.dual_steenrod_algebra import DualSteenrodAlgebra
    sage: from yacop.modules.functors import truncation
    sage: C=__newres(SteenrodAlgebra(3),shared=True)
    sage: W=truncation(DualSteenrodAlgebra(3),tmin=-12,emin=-5)
    sage: E=SmashResolution(W,C)
    sage: E.compute(smax=3,nmax=6,quiet=True)

"""
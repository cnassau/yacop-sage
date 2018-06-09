# Steenrod algebra resolutions for the complex motivic case
#
# Copyright (C) 2018 Christian Nassau <nassau@nullhomotopie.de>
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License version 2 as
# published by the Free Software Foundation.

oo::class create yacop::motc_resolver {
    superclass ::yacop::gfr_resolver

    variable algebrareg profilechoice sdeg edeg ideg profile genlists prime

    constructor {} {
	next
	steenrod::monomap motcurr
	steenrod::enumerator MotPrev
    }

    method setAlgebra {prime algmono} {
	if {$prime != 2} {
	    error "motivic resolver works only at the prime 2"
	}
	foreach {cf e r g} $algmono break
	if {$e} {
	    error "motivic resolver expects exterior part = zero"
	}
	set algebrareg $algmono
	set r2 {}
	set p 1
	foreach x $r {
	    if {$x>0} {
		lappend r2 [expr {$x-1}]
		incr e $p
	    }
	    set p [expr {$p<<1}]
	}
	next $prime [list $cf $e $r2 $g]
    }

    method setGenlist {enum data} {
	next $enum $data
    }

    method fillMonomap {suff sdegree} {
	# read differentials from the database
	set mapname mm$suff
	$mapname clear
	if {$suff eq "curr"} {
	    motcurr clear
	}
	db eval  {
	    select
	    srcgen.id as srcid,
	    targen.id as tarid,
	    srcgen.edeg as srcedeg,
	    targen.edeg as taredeg,
	    frag.opedeg as opedeg,
	    frag_decode(frag.format,frag.data) as poly
	    from fragments as frag
	    join generators as srcgen on srcgen.rowid = frag.srcgen
	    join generators as targen on targen.rowid = frag.targen
	    where frag.srcgen in (select rowid from generators where sdeg = $sdegree)
	} values {
	    if {$values(taredeg) + $values(opedeg) == $values(srcedeg)} {
		set m [list 1 0 {} $values(srcid)]
		$mapname append $m $values(poly)
	    }
	    if {$suff eq "curr"} {
		set m [list 1 0 {} $values(srcid)]
		motcurr append $m $values(poly)
	    }
	}
	if 0 {
	    my dumpMonomap $mapname
	    if {$suff eq "curr"} {
		my dumpMonomap motcurr
	    }
	}
    }

    method dumpMonomap {mmp} {
	puts ":: $mmp"
	foreach {id target} [$mmp list] { puts " $mmp $id -> $target" }
    }

    method setTridegree {s i e} {
	#puts "TRIDEG $s $i $e"
	next $s $i $e
    }

    method setmaxprofile {profmode} {
	#set profmode none
	set profilechoice $profmode
	#puts "profmode=$profmode"
	next $profmode
    }

    method ComputeMatrix {src map dst} {
	if {[catch {steenrod::ComputeMatrix $src $map $dst} errmsg options]} {
	    puts "$src = [$src configure]"
	    puts "$dst = [$dst configure]"
	    puts "$src = [$src basis]"
	    puts "$dst = [$dst basis]"
	    foreach {id tar} [$map list] {
		puts "$map  $id -> $tar"
	    }
	    return -options $options $errmsg
	}
	return $errmsg
    }

    method make-corrections {matvar basvar diffsvar errorvar} {
	upvar 1 $matvar mdsc $basvar bas $errorvar errors $diffsvar diffs
	set ecnt 0
	while {$ecnt < [llength $errors]} {
	    set idlist [lindex $errors $ecnt]
	    incr ecnt
	    set islastbatch [expr {$ecnt+1 == [llength $errors]}]
	    set errterms [lindex $errors $ecnt]
	    if {[catch {
		set seqmap [MotPrev motseqno Cprev]
	    } errmsg options]} {
		puts [MotPrev basis]
		puts [MotPrev configure]
		return -options $options $errmsg
	    }
	    set errmat [steenrod::matrix extract cols $errterms $seqmap]
	    foreach {er ec} [steenrod::matrix dimensions $errmat] break
	    if {0==$er || 0==$ec || [steenrod::matrix iszero $errmat]} {
		incr ecnt
		continue
	    }
	    set lft [steenrod::matrix lift $prime $mdsc $bas errmat]
	    if {![steenrod::matrix iszero $errmat]} {
		# The lift is allowed to fail if the current generator supports a
		# differential d(g) = h + ... and h has not yet been computed.
		# This can happen if we're working at (s,t) but (s-1,t) has not
		# been done yet (only (s-1,t-1)). We then need to introduce the
		# target generator now.
		error "lift failed (x)"
	    }
	    set cnt 0
	    set corrections {}
	    foreach id $idlist {
		set preim [steenrod::matrix extract single-row $lft $cnt]
		set aux [Ccurr decode $preim -1]
		steenrod::poly varappend diffs($id) $aux
		if {$islastbatch} {
		    mmnext set [list 0 0 0 $id] $diffs($id)
		}
		lappend corrections $aux
		unset aux
		incr cnt
	    }
	    # update error terms
	    steenrod::matrix addto errterms [steenrod::ComputeImageMotivic motcurr MotPrev $corrections] 1 $prime
	    lset errors $ecnt $errterms
	    incr ecnt
	}
    }

    method resolve-step {genvar diffvar errvar} {
	upvar 1 $genvar gens $diffvar diffs $errvar errors

	foreach vname {prev curr next} {
	    C$vname configure -edeg $edeg -ideg $ideg -profile $profile
	    C$vname sigreset
	    C$vname configure -genlist [set genlists($vname)]
	}

	set sc $sdeg
	set sp [expr {$sdeg-1}]
	set sn [expr {$sdeg+1}]

	yacop::logvars sc sp sn edeg

	if {0 == $sc} {
	    # fake appropriate matrix
	    if {($edeg==0) && ($ideg==0)} {
		set mdsc 1
	    } else {
		# here C-1 = F_p = 0. create a zero matrix with the
		# right number of rows.
		set mdsc [steenrod::matrix convert2 [steenrod::matrix create [Ccurr dim] 1]]
	    }
	    set mdsn [my ComputeMatrix Cnext mmnext Ccurr]
	} else {
	    set mdsc [my ComputeMatrix Ccurr mmcurr Cprev]
	    set mdsn [my ComputeMatrix Cnext mmnext Ccurr]
	}

	yacop::logdbg "computed mdsc and mdsn"

	steenrod::matrix ortho $prime mdsn ker  ;# (ker is not used)
	steenrod::matrix ortho $prime mdsc ker bas
	steenrod::matrix quot $prime ker $mdsn
	unset mdsn ;# (to save memory)

	set ngen [lindex [steenrod::matrix dimensions $ker] 0]
	set genlist {}
	set newdiffs {}

	# We need $ngen new generators, and so far we only know the
	# signature-zero part of their differentials.

	set id [llength [Cnext cget -genlist]]
	for {set i 0} {$i<$ngen} {incr i} {
	    set vct [steenrod::matrix extract single-row $ker $i]
	    lappend newdiffs [Ccurr decode $vct]
	    lappend genlist $id
	    #puts "GEN $id     => [lindex $newdiffs end] + ..."
	    incr id
	}
	unset -nocomplain vct ;# to save memory
	unset -nocomplain ker ;# to save memory

	# introduce new generators:
	foreach id $genlist df $newdiffs {
	    lappend gens [list $id [expr {$sdeg+1}] $ideg $edeg]
	    set diffs($id) $df
	    lappend genlists(next) [list $id $ideg $edeg 0]
	    mmnext set [list 0 0 0 $id] $diffs($id)
	}

	lappend errors $genlist [steenrod::ComputeImageMotivic motcurr MotPrev $newdiffs]

	my make-corrections mdsc bas diffs errors

	set corrections {}
	set errterms {}

	set upcnt 0
	while {[Cprev signext]} {
	    incr upcnt
	    # if {![expr {$upcnt & 0x7f}]} ::yacop::ProgressHandler

	    set sig [Cprev cget -signature]
	    Ccurr configure -signature $sig
	    Cnext configure -signature $sig
	    incr dimcnt [Cprev dim]
	    set mdsc [my ComputeMatrix Ccurr mmcurr Cprev]
	    steenrod::matrix ortho $prime mdsc "" bas
	    my make-corrections mdsc bas diffs errors
	}

	yacop::logvars fulldim dimcnt

	set allzero 1
	foreach {genlist errterms} $errors {
	    if {![steenrod::matrix iszero $errterms]} {
		set allzero 0
		break
	    }
	}
	if {$allzero && $edeg > $sdeg+1} {
	    # all error terms are zero and no new generators possible
	    return -code break
	}
    }

    method resolve {} {
	set gl {}
	set dfs {}
	my variable ideg sdeg edeg genlists prime algebra algebrareg

	# MotPrev is the space where d(d(newgen)) lives during the correction process
	set glmot {}
	foreach itm $genlists(prev) {
	    foreach {id i e} $itm break
	    lappend glmot [list $id [expr {2*$i}] 0]
	}
	MotPrev configure -prime $prime -algebra $algebrareg -ideg [expr {2*$ideg}] -edeg 0 -genlist $glmot

	# the resolution loop uses 3 variables
	set gens {}              ;# list of tuples (id, sdeg, ideg, edeg) for each new generator
	unset -nocomplain diffs  ;# array id -> differential of the new generator
	set errors {}            ;# alternating list of "(id1,...,idk)" and "matrix of dd(id1),..,dd(idk)"

	for {set edeg 0} {true} {incr edeg} {
	    my setmaxprofile $profilechoice
	    my resolve-step gens diffs errors
	    if {$edeg>$sdeg + 1000} {
		error "internal error: edeg much too big $edeg >> $sdeg"
	    }
	}

	foreach itm $gens {
	    set id [lindex $itm 0]
	    #puts "ZZZ $itm -> $diffs($id)"
	    lappend dfs $diffs($id)
	}

	foreach {idlist errterms} $errors {
	    if {![steenrod::matrix iszero $errterms]} {
		puts "ids=$idlist"
		puts errterms=\n[join $errterms \n]
		foreach row $errterms {
		    puts "> [MotPrev decode $row]"
		}
		error "internal error: error terms not reduced to zero"
	    }
	}

	return [list $gens $dfs]
    }


}

#
# Sage related material
#
# Copyright (C) 2009 Christian Nassau <nassau@nullhomotopie.de>
#
#  $Id: sage.tcl,v 1.3 2009/05/09 20:44:00 cn Exp $
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License version 2 as
# published by the Free Software Foundation.
#

package require yacop 1.0

if 0 {
    rename steenrod::matrix steenrod::matrix.oow
    proc steenrod::matrix args {
	if {[lindex $args 0] eq "lift"} {
	    #puts $args
	}
	uplevel 1 steenrod::matrix.oow $args
    }
} 

namespace eval yacop::sage {
    
    # if sage re-loads the yacop package we can still get
    # calls from a previous session (e.g. destructors). 
    # we should try to make sure our new namespaces get ids that are 
    # unique to this session
    set Epoch [clock seconds]

    proc new-namespace {} {
	variable nspCnt
	variable Epoch
	set snm yacop-$Epoch-[incr nspCnt] 

        set snm ::$snm
        namespace eval $snm {}
        proc $snm {eval script} {
            if {$eval ne "eval"} barf
            uplevel 1 [namespace code $script]
        }

	return $snm
    }

    proc sqlitefuncs {args} {
	foreach func {
	    pylist pydict pymatrix
	    sagepoly_even
	    sagepoly_odd
	    sagepoly_even_PtsOnly
	    sagepoly_odd_PtsOnly
	} {
	    uplevel 1 $args function $func ::yacop::sage::$func
	}
    }
    proc pymatrix {mat} {
        set res {}
        foreach row $mat {
            lappend res "\[[join $row ,]\]"
        }
        return "\[[join $res ,]\]"
    }
    proc pylist args {
	return "([join $args ,])"
    }
    proc pydict args {
	set aux {}
	foreach {key val} $args {
	    lappend aux \"$key\":$val
	}
	return "{[join $aux ,]}"
    }
    foreach a {odd even} b {P Sq} {
	foreach x {_PtsOnly {}} y {1 0} {
	    interp alias {} ::yacop::sage::sagepoly_$a$x {} ::yacop::sage::sagepoly $b $y
	}
    }
    proc bitlist {val} {
	set res {}
	set idx 0
	while {$val} {
	    if {$val & 1} {
		lappend res $idx
	    }
	    incr idx
	    set val [expr {$val>>1}]
	}
	return $res
    }
    proc ::tcl::mathfunc::bitcount {x} {
	set bx [expr {$x - (($x>>1)&0x77777777) - (($x>>2)&0x33333333) - (($x>>3)&0x11111111)}]
	expr {(($bx + ($bx >> 4)) & 0x0f0f0f0f) % 255}
    }
    proc sagepoly {opsym ptsonly prime data {targen {}}} {
	set res {}
	if {$ptsonly} {
	    set powers [steenrod::prime $prime powers]
	}
	foreach smd $data {
	    foreach {coeff ext red stuff} $smd break
	    if {$ptsonly} {
		set a [expr {bitcount($ext)}]
		if {$a>1} continue
		if {$a==1} {
		    # reduced part has to be zero
		    set fail 0
		    foreach x $red {
			if {$x} {
			    set fail 1
			    break
			}
		    }
		    if {$fail} continue
		} else {
		    # reduced part has to consist of exactly one prime power
		    set cnt 0
		    foreach x $red {
			if {$x} {
			    if {$x in $powers} {
				incr cnt
			    } else {
				# nonzero and not a prime power => bad
				incr cnt 10
			    }
			}
			if {$cnt>1} break
		    }
		    if {$cnt!=1} continue 
		}
	    }
	    if {$ext} {
		append coeff * A.Q([join [bitlist $ext] ,])
	    }
	    if {1||[llength $red]} {
		append coeff * A.$opsym ([join $red ,])
	    }
	    append res + $coeff
	}
	if {$res eq ""} return
	if {$targen ne ""} {
	    return "($res,self.g(id=$targen))"
	} 
	return $res
    }
}

package provide yacop::sage 1.0


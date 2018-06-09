#
# Common stuff
#
# Copyright (C) 2009-2018 Christian Nassau <nassau@nullhomotopie.de>
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License version 2 as
# published by the Free Software Foundation.
#

namespace eval yacop {

    # granularity for sqlite's progress handler
    set dbprogsteps 5000

    # steenrod progress reporting granularity
    set ::steenrod::_progsteps 0x7

    proc progress {} {
	# overwrite this to install a custom progress handler
    }

    variable SIGINT 0

    proc interruptible {script} {
	steenrod::interruptible ::yacop::SIGINT {
	    uplevel 1 $script
	}
    }

    proc ProgressHandler {} {
	variable SIGINT
	if {$SIGINT} {
            while {$SIGINT} {
                steenrod::interruptible ::yacop::SIGINT {
                    # this clears the SIGINT variable
                }
            }
	    error "computation has been interrupted"
	}
	# invoke progress hook
	progress
    }

    variable progVar
    proc progVarTrace {args} {
        if {$::yacop::SIGINT} {
            set ::steenrod::interrupt 1
        }
        ::yacop::progress
    }
    trace add variable ::yacop::progVar write ::yacop::progVarTrace

    namespace eval sqlitefunctions {
        proc frag_decode {fmt data {targen {}}} {
            switch -- $fmt {
                bin { set data [steenrod::binfmt decode $data] }
                tcl { }
                z { set data [zlib inflate $data] }
                default {
                    error "unknown format '$fmt'"
                }
            }
            if {$targen ne ""} {
                set daux {}
                foreach m $data {
                    lset m end $targen
                    lappend daux $m
                }
                set data $daux
            }
            return $data
        }
        proc frag_encode_z {data} { zlib deflate $data 9 }
	proc opcoeff op {lindex $op 0 0}
    }
}

#
# Logging
#
# Copyright (C) 2009 Christian Nassau <nassau@nullhomotopie.de>
#
#  $Id: logging.tcl,v 1.2 2009/05/09 20:44:00 cn Exp $
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License version 2 as
# published by the Free Software Foundation.
#

namespace eval yacop {
    proc logvars args {}
    proc logdbg args {}
    proc iflog args {}
    proc log args {}

    foreach loglevel {dbg err inf} {
	interp alias {} ::yacop::log$loglevel {} ::yacop::log $loglevel
    }
}

if {[info exists env(YACOPLOG)]} {
    
    puts "yacop logging enabled (YACOPLOG=$env(YACOPLOG))"
    switch -- $env(YACOPLOG) {
        stderr - stdout {
            set ::yacop::logfile $env(YACOPLOG)
        }
        default {
            set ::yacop::logfile [open $env(YACOPLOG) a]
        }
    }
    proc ::yacop::log {level message} {
        variable logfile
        upvar 1 this this
        set time [clock format [clock scan now] -format "%D %T"]
        if {[set lvl [expr {[info level]-1}]] == 0} {
            set msg ""
        } else {
            #incr lvl -1
            set msg [string repeat {  } $lvl]
            if {[info exists this]} {
                append msg "$this "
            }
            append msg [lindex [info level $lvl] 0] " > "
        }

        append msg $message
        puts $logfile [format {%-10s %-3s %s} $time $level $msg]
    }

    proc ::yacop::iflog {script} {uplevel 1 $script}

    proc ::yacop::logvars {args} {
        set vinfo {}
        foreach vname $args {
            upvar 1 $vname newname
            if {![info exists newname]} {
                lappend vinfo "$vname doesn't exist"
            } elseif {[array exists newname]} {
                set vlen 1
                set adat {}
                foreach key [lsort [array names newname]] {
                    set aux [format %s(%s) $vname $key]
                    if {[string length $aux] > $vlen} {
                        set vlen [string length $aux]
                    }
                    lappend adat $aux $newname($key)
                }
                set fmt "%-[expr {$vlen+1}]s= %s"
                foreach {a b} $adat {
                    uplevel 1 [list ::yacop::log var [format $fmt $a $b]]
                }

            } else {
                lappend vinfo "$vname=\"$newname\""
            }
        }
        if {[llength $vinfo]} {
            uplevel 1 [list ::yacop::log var [join $vinfo {, }]]
        }
    }

}


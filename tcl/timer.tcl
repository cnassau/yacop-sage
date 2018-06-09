#
# Timer routines
#
# Copyright (C) 2009 Christian Nassau <nassau@nullhomotopie.de>
#
#  $Id: timer.tcl,v 1.2 2009/05/09 20:44:00 cn Exp $
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License version 2 as
# published by the Free Software Foundation.
#

namespace eval ::yacop::timer {
      
    switch -- $::tcl_platform(os) {
        Linux {
            if {![file exists /proc/self/stat]} {
		proc now {} now-fallback
            } else {
		# read the file once and find the last ")" - this delimits
		# the process name. see "man 5 proc" for more info.
		set ch [open /proc/self/stat]
		set data [read $ch]
		close $ch
   		regexp "^(.*\\))\[^)\]+\$" $data -> aux
		# now let "now" skip the first [string length $aux] bytes
		proc now {} [string map "%%START%% [string length $aux]" {
                    set ch [open /proc/self/stat]
                    set data [read $ch]
                    close $ch
		    set aux [string range $data %%START%% end]
		    # return sum of user and kernel mode seconds
		    set ujiffies [lindex $aux 11]
                    set kjiffies [lindex $aux 12]
                    return [expr {($ujiffies+$kjiffies) / 100.0}]
                }]
            }
        }
        SunOS {
            set fname [file join /proc [pid] usage]
            if {![file exists $fname]} {
                proc now {} now-fallback
            } else {
                
                switch -- $::tcl_platform(byteOrder) {
                    "bigEndian" { set fmt "W" }
                    "default"   { set fmt "w" }
                }

                set map [list %%FNAME%% $fname %%FMT%% $fmt]
                
                # "man -s 4 proc" has a description of struct_prusage 
                
		proc now {} [string map $map {
                    set ch [open %%FNAME%%]
                    fconfigure $ch -encoding binary
                    set data [read $ch]
                    close $ch
                    set pr_utime [string range $data 40 47]
                    binary scan $pr_utime %%FMT%% usertime
                    expr {0.0000000001 * $usertime}
                }]
            } 
        }   
        default {
	    proc now {} now-fallback
        }
    }
    
    proc now-fallback  {} {
        expr {0.001 * [clock clicks -milliseconds]}
    }
    
    proc start {} {
        upvar 1 __yacop_timer__ starttime 
	set starttime [now]
    }
    
    proc stop {} {
	upvar 1 __yacop_timer__ starttime 
        set stoptime [now]
        if {![string length $stoptime]} {
            return -1
        }
        return [format %.2f [expr {$stoptime - $starttime}]]
    }
    
    namespace export start stop
    namespace ensemble create
}

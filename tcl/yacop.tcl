# Yacop startup file
#
# Copyright (C) 2009-2018 Christian Nassau <nassau@nullhomotopie.de>
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License version 2 as
# published by the Free Software Foundation.
#

# external requirements first

package require Tcl 8.6.8
package require TclOO 1
package require sqlite3 3.21
package require Steenrod 2.0

# source yacop files

foreach file {
    logging.tcl
    common.tcl
    prefs.tcl
    timer.tcl
    gfr.tcl
    motc.tcl
    smasher.tcl
    chart.tcl
    pschart.tcl
    chmap.tcl
} {
    source [file join [file dirname [info script]] $file]
}

# create a wrapper around sqlite which installs the default
# busy and progress handler:

namespace eval ::yacop::sectionizer {
    variable quiet 0
    proc quiet {newval} {
	variable quiet $newval
    }
    proc StatusMsg {stuff} {
	variable indent
	variable quiet
	if {$quiet} return
	puts "[string repeat {  } [expr {$indent-1}]]> $stuff"
    }
    proc Section {title code} {
	variable indent
	incr indent 1
	StatusMsg $title
	uplevel 1 $code
	incr indent -1
    }
    proc BusyCB {cnt} {
	variable busycnt
	if {[incr busycnt] % 30 == 0} {
	    catch {::yacop::sectionizer::Section "waiting for database lock" {}}
	}
	catch {update}
	after 100
	if {$::yacop::SIGINT} {
	    return 1
	}
	return 0
    }
    namespace export {[a-z]*}
    namespace ensemble create
}

proc yacop::sqlite {dbname {filename :memory:}} {
    uplevel 1 ::sqlite3 $dbname $filename -uri on
    uplevel 1 $dbname busy ::yacop::sectionizer::BusyCB
    uplevel 1 $dbname progress $::yacop::dbprogsteps ::yacop::ProgressHandler
    foreach tclfunc {
        list lindex
    } {
        uplevel 1 $dbname function $tclfunc ::$tclfunc
    }
    foreach cmd [info commands {::yacop::sqlitefunctions::[a-z]*}] {
        uplevel 1 $dbname function [namespace tail $cmd] $cmd
    }
    if {[package present yacop::sage]} {
        uplevel 1 [list ::yacop::sage::sqlitefuncs $dbname]
    }
}

package provide yacop 1.0

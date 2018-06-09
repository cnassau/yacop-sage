#
# User preference database
#
# Copyright (C) 2009 Christian Nassau <nassau@nullhomotopie.de>
#
#  $Id: prefs.tcl,v 1.5 2009/05/31 10:59:53 cn Exp $
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License version 2 as
# published by the Free Software Foundation.
#

namespace eval yacop::prefdb {
    # directory for user config file
    set path ~/.yacop
}

if {$::tcl_platform(platform) eq "windows"} {
    catch {
        package require twapi
        set yacop::prefdb::path \
            [file join [twapi::get_shell_folder csidl_common_appdata] Yacop]
    }
}

namespace eval ::yacop::prefdb {

    file mkdir $path
    sqlite3 ::yacop::prefdb::db [file join $path prefs.db]
    
    ::yacop::prefdb::db eval {
        create table if not exists config(unit text,varname text,value text);
        create unique index if not exists config_idx1 on config(unit,varname); 
    }
    
    proc trace {unit var fullname} {
        ::yacop::prefdb::db eval {
            select value from config where unit=$unit and varname=$var
        } {
            set $fullname $value
        }
        ::trace add variable $fullname write \
            "[list ::yacop::prefdb::writevar $unit $var $fullname] ;#"
    }

    proc writevar {unit varname fullname} {
        set newval [set $fullname]
        ::yacop::prefdb::db eval {
            insert or replace into config(unit,varname,value)
            values($unit,$varname,$newval)
        } {
            set $fullname $value
        }
    }

    namespace export trace
    namespace ensemble create
}
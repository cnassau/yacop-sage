# Steenrod algebra ground field resolutions
#
# Copyright (C) 2009-2018 Christian Nassau <nassau@nullhomotopie.de>
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License version 2 as
# published by the Free Software Foundation.

oo::class create yacop::gfr_resolver {

    variable {*}{
	sdeg ideg edeg profile prime algebra genlists
    }

    constructor {} {
	set pth [namespace path]

	# we put the parent namespace into our search path
	# to make the database "db" accessible.
	lappend pth [uplevel 1 namespace current]

	# we use a separate namespace for our static methods
	namespace eval ::yacop::gfr_tools {}
	lappend pth ::yacop::gfr_tools

	namespace path $pth

	# create enumerators for the free modules
	foreach vname {prev curr next errcheck} {
	    steenrod::enumerator C$vname
	}

	# monomaps that represent the differentials
	steenrod::monomap mmcurr
	steenrod::monomap mmnext
    }

    method setTridegree {s i e} {
	set sdeg $s
	set ideg $i
	set edeg $e
    }

    method setAlgebra {Prime Algebra} {
	set prime $Prime
	set algebra $Algebra
	foreach vname {prev curr next errcheck} {
	    C$vname configure -prime $prime -algebra $algebra
	}
    }

    method setGenlist {suff gens} {
	set genlists($suff) $gens
    }

    method fillMonomap {suff sdegree} {
	# read differentials from the database
	set mapname mm$suff
	$mapname clear
	db eval  {
	    select
	    srcgen.id as srcid,
	    targen.id as tarid,
	    frag_decode(frag.format,frag.data) as poly
	    from fragments as frag
	    join generators as srcgen on srcgen.rowid = frag.srcgen
	    join generators as targen on targen.rowid = frag.targen
	    where frag.srcgen in (select rowid from generators where sdeg = $sdegree)
	} values {
	    set m [list 1 0 {} $values(srcid)]
	    $mapname append $m $values(poly)
	}
    }

    method setmaxprofile {{mode auto}} {
        set profile [findBestProfile [list [namespace which Ccurr]] \
                         $prime $algebra $sdeg $ideg $edeg $mode]
    }

    # the main resolver routine follows

    method resolve {} {

	foreach vname {prev curr next} {
	    C$vname configure -edeg $edeg -ideg $ideg -profile $profile
	    C$vname sigreset
	    C$vname configure -genlist [set genlists($vname)]
	}

	set sc $sdeg
	set sp [expr {$sdeg-1}]
	set sn [expr {$sdeg+1}]

	yacop::logvars sc sp sn

	if {0 == $sc} {
	    # fake appropriate matrix
	    if {($edeg==0) && ($ideg==0)} {
		set mdsc 1
	    } else {
		# here C-1 = F_p = 0. create a zero matrix with the
		# right number of rows.
		set mdsc [steenrod::matrix create [Ccurr dim] 1]
	    }
	    set mdsn [steenrod::ComputeMatrix Cnext mmnext Ccurr]
	} else {
	    set mdsc [steenrod::ComputeMatrix Ccurr mmcurr Cprev]
	    set mdsn [steenrod::ComputeMatrix Cnext mmnext Ccurr]
	}

	yacop::logdbg "computed mdsc and mdsn"

	# compute image...
	steenrod::matrix ortho $prime mdsn ""  ;# (ker is not used)

	# compute kernel...
	steenrod::matrix ortho $prime mdsc ker

	unset mdsc ;# (to save memory)

	# ...and compute quotient
	steenrod::matrix quot $prime ker $mdsn

	unset mdsn ;# (to save memory)

	set ngen [lindex [steenrod::matrix dimensions $ker] 0]

	yacop::logvars ngen

	if {!$ngen} {
	    # no new generators needed
	    return {{} {}}
	}

	# We need $ngen new generators, and so far we only know the
	# signature-zero part of their differentials.

	set id [llength [Cnext cget -genlist]]

	set genlist {}
	set newdiffs {}
	for {set i 0} {$i<$ngen} {incr i} {
	    set vct [lindex [steenrod::matrix extract row $ker $i] 0]
	    lappend newdiffs [Ccurr decode $vct]
	    lappend genlist $id
	    incr id
	}

	unset -nocomplain vct ;# to save memory
	unset -nocomplain ker ;# to save memory

	# We use an auxiliary enumerator as a reference for error vectors.
	# This one agrees with C$sp except that it has empty profile

	foreach parm [Cprev configure] {
	    Cerrcheck configure [lindex $parm 0] [lindex $parm 1]
	}
	Cerrcheck configure -profile {}

	# these counters are used for error detection
	set dimcnt  [Cprev dim]
	set fulldim [Cerrcheck dim]

	# The rows in the matrix errterms are "d(d($id))" so they
	# should be zero at the end of the correction process

	set errterms [steenrod::ComputeImage mmcurr Cerrcheck $newdiffs]
	yacop::logvars newdiffs errterms

	yacop::logdbg "beginning correction process"

	# now correct errorterms by induction on signature

	set upcnt 0

	while {[Cprev signext]} {

	    incr upcnt

	    # if {![expr {$upcnt & 0x7f}]} ::yacop::ProgressHandler

	    set sig [Cprev cget -signature]
	    Ccurr configure -signature $sig
	    Cnext configure -signature $sig

	    incr dimcnt [Cprev dim]

	    yacop::logvars upcnt sig dimcnt

	    #puts "$dimcnt / $sig"

	    # extract errors of this signature:
	    set seqmap [Cerrcheck seqno Cprev]
	    set errmat [steenrod::matrix extract cols $errterms $seqmap]

	    yacop::logdbg "have errmat"

	    # compute relevant part of matrix   $Ccurr -> $Cprev
	    set mdsn [steenrod::ComputeMatrix Ccurr mmcurr Cprev]

	    yacop::logdbg "have mdsn"

	    # compute lift
	    set lft [steenrod::matrix liftvar $prime mdsn errmat]

	    unset mdsn

	    yacop::logdbg "have lift"

	    set cnt 0
	    set corrections {}
	    foreach id $genlist {
		set preim [steenrod::matrix extract single-row $lft $cnt]
		lappend corrections [set aux [Ccurr decode $preim -1]]
		set aux2 [lindex $newdiffs $cnt]
		lset newdiffs $cnt dummy ;# to free a refcount on $aux2
		steenrod::poly varappend aux2 $aux
		lset newdiffs $cnt $aux2
		unset aux2
		incr cnt
	    }
	    yacop::logdbg "corrections applied"

	    # update error terms
	    steenrod::matrix addto errterms [steenrod::ComputeImage mmcurr Cerrcheck $corrections] 1 $prime
	    yacop::logdbg "error terms updated"
	}

	yacop::logvars fulldim dimcnt

	# check that signature decomposition was complete
	if {$fulldim != $dimcnt} {
	    error "signatures not correctly enumerated"
	}

	# check that error terms really are zero
	if {![steenrod::matrix iszero $errterms]} {
	    yacop::logvars errterms
	    if 1 {
		puts profile=$profile
		puts "error terms decoded:"
		foreach x $errterms {
		    puts "  : [Cerrcheck decode $x]"
		}
	    }
	    error "error terms not reduced to zero"
	}

	# introduce new generators:

	set gl {}
	foreach id $genlist df $newdiffs {
	    lappend gl [list $id [expr {1+$sdeg}] $ideg $edeg]
	    lappend genlists(next) [list $id $ideg $edeg 0]
	    mmnext set [list 0 0 0 $id] $df
	}

	return [list $gl $newdiffs]
    }
}

namespace eval ::yacop::gfr_tools {

    proc findBestProfile {enumerators prime algebra sdeg ideg edeg {mode auto}} {
	# find the best applicable subalgebra at this tridegree. this is
	# probably the one that gives the smallest vector space dimension.
	# so we look for the biggest admissible profiles from both above
	# and below, then count the dimensions and take the smaller one.
	#
	# the underlying theory is hidden in "Ein neuer Algorithmus
	# zur Untersuchung der Kohomologie der Steenrod-Algebra",
	# Logos Verlag Berlin 2002, ISBN 3-89722-881-5

	set sdeg2 $sdeg
	incr sdeg2 0

	switch -- $mode {
	    "none" {
		set profile {0 0 0 0}
	    }
	    "upper" {
		set profile [maxupperprofile $prime $algebra $sdeg2 $ideg $edeg]
	    }
	    "lower" {
		set profile [maxlowerprofile $prime $algebra $sdeg2 $ideg $edeg]
	    }
	    "auto" {
		set uprof [maxupperprofile $prime $algebra $sdeg2 $ideg $edeg]
		set lprof [maxlowerprofile $prime $algebra $sdeg2 $ideg $edeg]
		foreach C $enumerators {
		    $C configure -edeg $edeg -ideg $ideg
		    $C configure -profile $uprof -signature {}
		    set updim [$C dimension]
		    $C configure -profile $lprof -signature {}
		    set lodim [$C dimension]
		    #puts "$C: updim=$updim lodim=$lodim"
		}
		if {$updim > $lodim} {
		    set profile $lprof
		} else {
		    set profile $uprof
		}
	    }
	    default {
		error "mode must be none, upper, lower, or auto"
	    }
	}
	return $profile
    }

    # here we determine the biggest profiles of subalgebras
    # that are applicable in a given tri-degree.

    proc maxupperprofile {prime algebra s ideg edeg} {
	yacop::logvars prime algebra s ideg edeg

	set edegs [steenrod::prime $prime edegrees]
	set rdegs [steenrod::prime $prime rdegrees]
	set tpmo  [steenrod::prime $prime tpmo]

	set NALG [llength $rdegs]

	set edat 0
	set rdat {}

	foreach dg $rdegs {
	    set slope [expr $tpmo * $dg]
	    if {($slope * $s) > $ideg} {
		lappend rdat $NALG
	    } else {
		lappend rdat 0
	    }
	}

	set bit 1
	foreach dg $edegs {
	    set slope $dg
	    if {($slope * $s) > $ideg} {
		set edat [expr {$edat | $bit}]
	    }
	    set bit [expr {$bit << 1}]
	}

	yacop::logvars edat rdat
	return [list 0 $edat $rdat 0]
    }


    proc maxlowerprofile {prime algebra s ideg edeg} {
	yacop::logvars prime algebra s ideg edeg
	set lowerprofile [maxlowerprofile.impl $prime $algebra $s $ideg $edeg]
	yacop::logvars lowerprofile
	return $lowerprofile
    }

    proc maxlowerprofile.impl {prime algebra s ideg edeg} {
	incr s 1

	set pows  [steenrod::prime $prime powers]
	set edegs [steenrod::prime $prime edegrees]
	set rdegs [steenrod::prime $prime rdegrees]
	set tpmo  [steenrod::prime $prime tpmo]
	set NALG  [llength $rdegs]

	if {$algebra=={}} {
	    set aux {}
	    foreach dg [steenrod::prime $prime rdegrees] { lappend aux $NALG }
	    set algebra [list 0 -1 $aux 0]
	}

	set ae [lindex $algebra 1]
	set ar [lindex $algebra 2]

	# ext and red describe the profile of the used subalgebra B
	set ext 0
	set red {}
	foreach dg [steenrod::prime $prime rdegrees] { lappend red 0 }

	# dB is the maximal slope, tB the maximal dimension of B
	set dB 0
	set tB 0
	set bit 1
	for {set i 0} {1} {incr i} {
	    yacop::logvars i dB tB

	    if {$i > 10} {
		# we're through with the entire algebra
		# so just return what we've got so far
		return [list 0 $ext $red 0]
	    }

	    if {[set slope [lindex $edegs $i]] > $ideg} {
		# cannot increase B for dimensional reasons, so return
		return [list 0 $ext $red 0]
	    }

	    if {$bit & $ae} {

		incr tB $slope
		if {$slope > $dB} { set dB $slope }

		if {($ideg - $tB - $s * $dB) < 0} {
		    # next profile too big, so return current one
		    return [list 0 $ext $red 0]
		}

		set ext [expr {$ext | $bit}]
	    }

	    for {set j $i} {[incr j -1] >= 0} {} {

		set arx [lindex $ar $j]
		set rdx [lindex $red $j]

		if {$arx eq ""} {set arx 0}
		if {$rdx eq ""} {set rdx 0}

		# if there's no more room in the $algebra, just continue
		if {$rdx >= $arx} {
		    yacop::logvars rdx arx ar red j
		    continue
		}

		# find slope of vanishing line for P_{j,rdx} - which is
		# (1/2) * ( degree P_{j,rdx} + degree P_{j,rdx}^{p-1} )

		set degree [expr {($tpmo * [lindex $rdegs $j])
				  * [lindex $pows $rdx]}]

		set slope [expr {$degree * $prime / 2}]

		yacop::logvars j rdx degree slope

		if {$slope > $dB} { set dB $slope }
		incr tB [expr {$degree * ($prime - 1)}]

		if {($ideg - $tB - $s * $dB) < 0} {
		    # next profile too big, so return current one
		    return [list 0 $ext $red 0]
		}

		lset red $j [expr {$rdx + 1}]
	    }

	    set bit [expr {$bit << 1}]
	}

	error not-reached!
    }
}

oo::class create yacop::gfr_generator_writer {

    # a little helper that writes differentials into the fragment table

    variable db prime algmono tmpdat lastgen

    constructor {dbcmd} {
        set db $dbcmd
	steenrod::enumerator enum
	proc writefuncDispatcher {monomial} {
	    my writefunc $monomial
	    return -code continue
	}
    }

    method add {p amo id s i e diff} {
	#puts "new gen $id ($s,$i,$e) -> $diff"
	set prime $p
	set algmono $amo
	$db eval {
	    insert into generators(id,sdeg,ideg,edeg)
	    values($id, $s, $i, $e)
	}
	set lastgen ""
	foreach varname {id s e i} {
	    set tmpdat($varname) [set $varname]
	}
	set tmpdat(srcsdeg) $s
	set tmpdat(tarsdeg) [expr {$s-1}]
	steenrod::poly split $diff [namespace current]::writefuncDispatcher
	my writepiece
    }

    method writefunc {monomial} {
	set x [steenrod::mono gen $monomial]
	set y [steenrod::mono edegree $monomial]
	if {($x != $lastgen) || ($y != $tmpdat(edeg))} {
	    my writepiece
	    set lastgen $x
	    set tmpdat(targetpiece) [steenrod::poly create]
	    set tmpdat(ideg) [steenrod::mono degree $prime $monomial]
	    set tmpdat(edeg) [steenrod::mono edegree $monomial]
	    enum configure -prime $prime -algebra $algmono \
		-genlist [list [list $lastgen 0 0 0]] \
		-ideg $tmpdat(ideg) -edeg $tmpdat(edeg)
	}
	steenrod::poly varappend tmpdat(targetpiece) [list $monomial]
    }

    method fragment_add {srcsdeg srcid tarsdeg tarid opideg opedeg data} {
        set format tcl
        if {[string length $data]>50} {
	    # TODO: check whether ztcl wouldn't be a better choice (and more compatible with python)
            set format bin
            set data [steenrod::binfmt encode $data]
        }
	$db eval {
	    insert into fragments(srcgen,targen,opideg,opedeg,format,data)
	    values( (select rowid from generators
		     where sdeg=$srcsdeg and id=$srcid),
		    (select rowid from generators
		     where sdeg=$tarsdeg and id=$tarid),
		    $opideg,$opedeg,$format,$data );
	}
    }

    method writepiece {} {
	if {![string length $lastgen]} return
	my fragment_add $tmpdat(srcsdeg) $tmpdat(id) $tmpdat(tarsdeg) \
	    $lastgen $tmpdat(ideg) $tmpdat(edeg) $tmpdat(targetpiece)
    }
}

# ---------------------------------------------------------------------------------------------------------
# ---------------------------------------------------------------------------------------------------------
# ---------------------------------------------------------------------------------------------------------
# ---------------------------------------------------------------------------------------------------------

oo::class create yacop::gfr {

    variable {*}{
        db profile prime algebra filename profmode algmon viewtype
    }

    export extend-to profmode algebra db viewtype lift

    method db {args} {
        if {[llength $args] == 0} {
            return $db
        }
	uplevel 1 [list $db] $args
    }

    method config {} {my db eval {select key,value from yacop_cfg}}

    method profmode {{newval {}}} {
	switch -- $newval {
	    {} {return $profmode}
	    auto - upper - lower - none {set profmode $newval}
	    default {error "unknown profile mode \"$newval\", should be auto, upper, lower, or none"}
	}
    }

    method viewtype {{newval {}}} {
        set types [my db eval {select name from chart_viewtypes order by name}]
        if {!($newval in $types)} {
            error "unknown viewtype \"$newval\", should be one of [join $types {, }]"
        }
        my db eval {insert or replace into yacop_cfg(key,value) values('viewtype',$newval)}
        my db eval {
            drop view if exists chart_generators;
            drop view if exists chart_fragments;
            drop view if exists chart_geninfo;
        }
        my db eval [my db onecolumn {select code from chart_viewtypes where name=$newval}]
    }

    method RegisterViewtypes {} {
        set common {
            create temporary view if not exists chart_fragments
            as select srcgen,targen,opideg,opedeg,frag_decode(format,data) as data from fragments;
        }
        if {$prime == 2 && [lindex $algebra 0] == 0} {
            set desc "Treat P(R) as Sq(R)"
            set code {
                create temporary view if not exists chart_generators as
                select rowid, sdeg, ideg/2-sdeg as ndeg, ideg/2 as ideg, edeg, basid from generators;
            }
            append code $common
            my db eval {insert or replace into chart_viewtypes(name,desc,code) values('even',$desc,$code)}
        }
        set desc "Standard view"
        set code {
            create temporary view if not exists chart_generators as
            select rowid, sdeg, ideg-sdeg as ndeg, ideg as ideg, edeg, basid from generators;
        }
        append code $common
        my db eval {insert or replace into chart_viewtypes(name,desc,code) values('odd',$desc,$code)}
	switch -- [GetConfigValue flavour regular] {
	    motivic {
		set desc "complex motivic"
		set code {
		    create temporary view if not exists chart_generators as
		    select rowid, sdeg, ideg-sdeg as ndeg, ideg as ideg, edeg, basid from generators;
		}
		append code $common
		my db eval {insert or replace into chart_viewtypes(name,desc,code) values('motivic',$desc,$code)}
	    }
	}
    }

    constructor {fname args} {

        set filename $fname
	set profmode auto
	set prime    ""
	set algebra  ""
	set flavour  regular

	yacop::sqlite [set db [namespace current]::db] $filename
	my db busy yacop::sectionizer::BusyCB

	namespace path [list {*}[namespace path] ::yacop::sectionizer]

	# create database if it doesn't already exist
	if {[catch {my db eval "select count(*) from yacop_cfg"}]} {
	    my db eval {

		create table if not exists yacop_cfg
		(key text unique, value text);

		insert or ignore into yacop_cfg(key,value)
		values('type','gfr');
		insert or ignore into yacop_cfg(key,value)
		values('flavour','regular');

		create table if not exists generators
		(/* the generators of the resolution */
		 rowid integer primary key,
		 id    integer,  /* sequence number in C<sdeg> */
		 basid integer,  /* sequence number in its bidegree */
		 sdeg  integer,  /* homological degree */
		 ideg  integer,  /* internal degree */
		 edeg  integer   /* exterior degree */);

		create unique index if not exists
		genlookup on generators(sdeg,ideg,id);
		create index if not exists
		gentridegree on generators(sdeg,ideg,edeg);

		create trigger if not exists
		generators_mkbasid after insert on generators
		when new.basid is NULL
		begin
		update generators
		set basid = (select count(*)-1 from generators
			     where sdeg = new.sdeg and ideg = new.ideg)
		where rowid = new.rowid;
		end;

		create table if not exists progress
		(/* information about the status of the computation */
		 sdeg integer unique /* homological degree */,
		 lastideg integer    /* last internal degree that has been completed  */);

		create table if not exists fragments
		(/* the summands of the differential */
		 rowid integer primary key,
		 srcgen integer, /* rowid of source generator */
		 targen integer, /* rowid of target generator */
		 opideg integer, /* internal degree of this piece */
		 opedeg integer, /* exterior degree of this piece */
		 format text,    /* how data is encoded */
		 data text       /* the data */);

		create view if not exists fragview
		as select rowid,srcgen,targen,opideg,opedeg,
		frag_decode(format,data) as data from fragments;

		create index if not exists fraglookupsrc
		on fragments(srcgen,targen);

		create index if not exists fraglookuptar
		on fragments(targen,srcgen);

		create index if not exists fraglookupideg
		on fragments(opideg);

		create table if not exists chart_viewtypes
		(name text unique, desc text, code text);
	    }
	}


	proc GetConfig {} {my db eval {select key,value from yacop_cfg}}
	proc SetConfig {dict} {
	    my db transaction {
		foreach {key value} $dict {
		    my db eval {
			insert or replace into yacop_cfg(key,value)
			values($key,$value)
		    }
		}
	    }
	}
	proc GetConfigValue {key {default {}}} {
	    array set aux [GetConfig]
	    if {[info exists aux($key)]} {
		return $aux($key)
	    }
	    return $default
	}
	proc SetConfigValue {key value} {
	    my db eval {
		insert or replace into yacop_cfg(key,value) values($key,$value)
	    }
	}

	# the user might accidentally run multiple resolver processes
	# on the same resolution. to protect against this we choose a unique
	# id for each process and store this in the database. new generators
	# are then only introduced if this id still matches.

        proc CommitHook {} {
	    variable writerid
	    if {![info exists writerid]} {return 0}
	    my db commit_hook ""
	    set wid [my db onecolumn {select value from yacop_cfg where key = 'writerid'}]
	    my db commit_hook [namespace code CommitHook]
	    if {$writerid ne $wid} {
		error "database has been hijacked (wid=$wid, self=$writerid)"
	    }
	    return 0
	}

	proc SetWriterId {} {
	    lappend x [info hostname] [pid]
	    lappend x [format %06x [expr {int(rand()*0xffffff)}]]
	    variable writerid [join $x -]
	    my db commit_hook ""
	    SetConfigValue writerid $writerid
	    my db commit_hook [namespace code CommitHook]
	}

	proc GetLastIdeg {sdeg} {
	    my db onecolumn {
		select ifnull(lastideg,-1) from progress where sdeg = $sdeg
	    }
	}

	proc SetLastIdeg {sdeg ideg} {
	    my db eval {
		insert or replace into progress(sdeg,lastideg) values($sdeg, $ideg)
	    }
	}

	proc GetGenlist {sdeg {cond {}}} {
	    set scmd "select id, ideg, edeg from generators where sdeg = \$sdeg"
	    if {[string length $cond]} {
		append scmd " and ($cond)"
	    }
	    append scmd " order by id"
	    lappend glist
	    my db eval $scmd result {
		lappend glist [list $result(id) $result(ideg) $result(edeg)]
	    }
	    return $glist
	}

	if {[GetConfigValue type] ne "gfr"} {
            error "yacop_cfg has wrong 'type' '[GetConfigValue type]': expected 'gfr'"
        }

	SetConfig $args

	set flavour [GetConfigValue flavour regular]
	switch -regexp $flavour {
	    regular {
		yacop::gfr_resolver create GFR
		yacop::gfr_generator_writer create Generator $db
	    }
	    motivic {
		yacop::motc_resolver create GFR
		yacop::gfr_generator_writer create Generator $db

		my db eval {
		    create table if not exists motr_smash_generators
		    -- elements of this table represent g*tau^a*rho^b
		    -- where g is a generator of the complex-motivic resolution
		    (rowid integer primary key,
		     motcgen integer,
		     tau integer,
		     rho integer);

		    create unique index if not exists motr_smash_gen_idx
		    on motr_smash_generators(motcgen,tau,rho);

		    create table if not exists motr_smash_fragments
		    (rowid integer primary key,
		     srcgen integer, /* rowid of source generator */
		     targen integer, /* rowid of target generator */
		     opideg integer, /* internal degree of this piece */
		     opedeg integer, /* internal degree of this piece */
		     format text,    /* how data is encoded */
		     data text       /* the data */);

		    create table if not exists motr_homology_cell
		    (rowid integer primary key,
		     sdeg integer,
		     ideg integer,
		     edeg integer,
		     ngens integer,
		     homtocycle text,
		     cycletohom text);

		    create unique index if not exists motr_homology_cell_idx
		    on motr_homology_cell(sdeg,ideg,edeg);

		    create table if not exists motr_homology_generators
		    (rowid integer primary key,
		     sdeg integer,
		     ideg integer,
		     edeg integer,
		     defn text);
		}

	    }
	    default {
		error "flavour $flavour not understood"
	    }
	}
	set prime [GetConfigValue prime]
	set algebra [GetConfigValue algebra]
        my RegisterViewtypes
    }

    method algebra {{Prime {}} {Algebra {}}} {
	if {$Prime eq "" && $Algebra eq ""} {
	    array set aux {
		prime {} algebra {}
	    }
	    array set aux [GetConfig]
	    return [list prime $aux(prime) algebra $aux(algebra)]
	}
	array set aux [GetConfig]
	if {[info exists aux(algebra)] || [info exists aux(prime)]} {
	    # check that new values agree with the information from the file
	    if {$Prime != $aux(prime)} {error "prime conflict: file has p=$aux(prime), you gave $Prime"}
	    if {![steenrod::algebra equal $Algebra $aux(algebra)]} {
		error "algebra conflict: file has \"$aux(algebra)\", you gave \"$Algebra\""
	    }
	    # algebras coincide => nothing to do
	    return
	}
	# test if $prime is prime
	steenrod::prime $Prime inverse 1
	set aux(prime) $Prime
	steenrod::algebra verify $Algebra
	set aux(algebra) $Algebra
	SetConfig [array get aux]
	set prime $Prime
	set algebra $Algebra
        my RegisterViewtypes
    }

    method motr-foreach-smash-gen {resvar limits bdy} {
	upvar 1 $resvar rho

	# limits can be specified for
	#   -  s    homological degree
	#   -  i    internal degree
	#   -  t    topological degreee  = i-s
	#   -  e    bockstein degree
	#   -  w    motivic weight       = (i-e)/2
	#   -  mw   Milnor-Witt          = t-w
	#
	#   - poscone / negcone    flags to switch positive, negative cone on/off

	array set l {
	    poscone 1
	    negcone 0
	}
	array set l $limits

	unset -nocomplain conds
	array set conds {
	    0 {}
	    1 {}
	    -1 {}
	}
	foreach v {s i t e w mw} dir {0 -1 -1 1 -1 1} {
	    set rid [expr {-$dir}]
	    if {[info exists l($v)]} {
		set l(${v}max) $l($v)
		set l(${v}min) $l($v)
	    }
	    if {[info exists l(${v}max)]} { lappend conds($dir) "${v}deg <= $l(${v}max)" }
	    if {[info exists l(${v}min)]} { lappend conds($rid) "${v}deg >= $l(${v}min)" }
	}

	set condgrow [join $conds(1) " AND "]
	set allconds [join [list {*}$conds(1) {*}$conds(-1) {*}$conds(0)] " AND "]

	if {$condgrow eq ""} {
	    error "not enough conditions to limit the generators: condgrow=$condgrow, allconds=$allconds"
	}

	puts condgrow=$condgrow
	puts allconds=$allconds

	SetWriterId

	my db eval {
	    select rowid, sdeg, ideg, edeg, ideg-sdeg as tdeg, (ideg-edeg)/2 as wdeg, (ideg-sdeg-(ideg-edeg)/2) as mwdeg from generators
	} h {
	    #parray h
	    # degrees:   s   i   t   e   w   mw
	    #     rho    0  -1  -1   1  -1   0
	    #     tau    0   0   0   2  -1   1

	    # FIXME: this is positive cone only right now

	    # the smallest allowed tau power is the weight of the generator
	    set tpow 0
	    foreach var {sdeg ideg tdeg edeg wdeg mwdeg} scale {0 0 0 2 -1 1} {
		set $var [expr {$h($var)+$tpow*$scale}]
	    }

	    # FIXME: using recursive CTE queries is overkill here (move this to Tcl)

	    # loop over tau powers
	    my db eval [subst {
		with tau(tpow,sdeg,ideg,tdeg,edeg,wdeg,mwdeg)
		as (
		    select :tpow,:sdeg,:ideg,:tdeg,:edeg,:wdeg,:mwdeg
		    union all
		    select 1+tpow,sdeg,ideg,tdeg,edeg+2,wdeg-1,mwdeg+1 from tau
		    where $condgrow
		    )
		select * from tau where $allconds
	    }] tau {
		#parray tau
		# loop over rho powers
		my db eval [subst {
		    with rho(rpow,sdeg,ideg,tdeg,edeg,wdeg,mwdeg)
		    as (
			select 0,:tau(sdeg),:tau(ideg),:tau(tdeg),:tau(edeg),:tau(wdeg),:tau(mwdeg)
			union all
			select  1+rpow,sdeg,ideg-1,tdeg-1,edeg+1,wdeg-1,mwdeg from rho
			where $condgrow
			)
		    select * from rho where $allconds
		}] rho {
		    #parray rho
		    set rho(motgen) $h(rowid)
		    set rho(motweight) $h(wdeg)
		    set rho(tpow) $tau(tpow)
		    uplevel 1 $bdy
		}
	    }
	}
    }

    method motr-compute-fragments {limits} {
	set debug on
	my motr-foreach-smash-gen sg $limits {

	    if {0 != $sg(rpow)} continue ;# just for debugging (?)

	    #parray sg
	    set taupow1 [expr {-$sg(motweight)}]
	    if {$debug} {
		set loc [my db onecolumn {select '  ('||sdeg||','||ideg||','||edeg||')' from generators where rowid = :sg(motgen)}]
		puts [format "looking for differentials on  tau^%d rho^%d g%d%s" $sg(tpow) $sg(rpow) $sg(motgen) $loc]
	    }
	    my db eval {
		select f.srcgen, f.targen, f.data, f.opideg, f.opedeg, (s.ideg-s.edeg)/2 as swdeg
		from fragview f join generators s on s.rowid = srcgen
		where targen = :sg(motgen)
		-- fixme: use available restrictions on the operations
	    } f {
		set taupow2 [expr {-$f(swdeg)}]
		steenrod::poly foreach [steenrod::poly motate $f(data)] m {
		    # now m is a summand op * taupow1 * targen of the differential d(taupow2 * srcgen)
		    #set f(smd) $m ; array set f [array get sg]; parray f
		    if {$debug} {
			puts [format "   diff smd has tau^%d g%d -> Sq(%s) * tau^%d g%d" $taupow2 $f(srcgen) [join [lindex $m 2] ,] $taupow1 $f(targen)]
			set J [expr {$sg(tpow)+$taupow1}]
			# check whether Sq(m) * x^{-J} is nonzero (where x in H^1 RP^infty)
			set cf 1
			set rsum 0
			foreach r [lindex $m 2] {
			    if {0 != ($rsum & $r)} {
				set cf 0
				break
			    }
			    incr rsum $r
			}
			if {$cf && ($rsum == (-$J & $rsum))} {
			    # nonzero
			    # now use tau^J = x^-J rho^J -> x^{-J+opideg} rho^J = tau^{J-opideg} rho^opideg
			    if {$f(opideg)<=$J} {
				set taudst [expr {-$taupow2 + $J - $f(opideg)}]
				set rhodst [expr {$sg(rpow) + $f(opideg)}]
				if {$debug} {
				    puts [format "  ->  tau^%d rho^%d g%d" $taudst $rhodst $f(srcgen)]
				}
			    }
			}
		    }
		}
	    }
	}
    }

    method novikov-extend {maxdim} {
	SetWriterId

        db eval {
            drop table if exists nofrags;
            drop table if exists nosquares;

            create table nofrags(rowid integer primary key,
                                 srcgen integer,
                                 targen integer,
                                 mu integer,
                                 v integer,
                                 data text,
                                 fmt text,
                                 opdeg integer,
                                 resdeg integer,
                                 diffidx integer);

            create table nosquares(rowid integer primary key,
                                   srcgen integer,
                                   targen integer,
                                   mu integer,
                                   v integer,
                                   data text,
                                   fmt text,
                                   resdeg integer);
        }

        my db progress $::yacop::dbprogsteps yacop::ProgressHandler
	#yacop::sectionizer::quiet off
        for {set dim 0} {$dim <= $maxdim} {incr dim} {
            Section "Novikov computation, dimension $dim" {
                my db transaction {
                    set ::steenrod::_progvarname ::yacop::progVar
                    yacop::interruptible {
                        my Novikov-dim $dim
                    }
                }
	    }
        }
    }

    method Novikov-dim {dim} [list source [file join [file dirname [info script]] nov.tcl]]

    method extend-to {limits} {

	array set aux [GetConfig]
	if {![info exists aux(prime)]} {
	    error "algebra not set"
	}

	variable prime $aux(prime) algebra $aux(algebra) algmon [steenrod::algebra tomono $algebra]

	GFR setAlgebra $prime $algmon

	set limitdict $limits
	unset -nocomplain limits
	array set limits $limitdict

	if {![info exists limits(sdeg)]} {
	    error "no limit for homological degree given"
	}

	if {![info exists limits(ideg)] &&
	    ![info exists limits(tdeg)] &&
	    ![info exists limits(rtdeg)]} {
	    error "no limit for internal or topological degree given"
	}

	SetWriterId

	# add initial generator if necessary
	if {0 == [my db onecolumn {select count(*) from generators where sdeg = 0}]} {
	    Generator add $prime $algmon 0 0 0 0 {}
	}

	for {set s 0} {$s < $limits(sdeg)} {incr s} {
	    set ideg 0x7ffffff
	    if {[info exists limits(tdeg)]} {
		set idegmax [expr {$limits(tdeg) + $s + 1}]
		if {$idegmax < $ideg} { set ideg $idegmax }
	    }
	    if {[info exists limits(rtdeg)]} {
		if {$prime != 2} {
		    error "rtdeg not possible for prime $prime"
		}
		if {[steenrod::mono exterior $algmon]} {
		    error "rtdeg cannot be used in presence of Bocksteins"
		}
		set idegmax [expr {2*$limits(rtdeg) + 2*$s + 3}]
		if {$idegmax < $ideg} { set ideg $idegmax }
	    }
	    if {[info exists limits(ideg)]} {
		set idegmax $limits(ideg)
		if {$idegmax < $ideg} { set ideg $idegmax }
	    }

	    set edeg [expr {$s+1}]
	    if {![steenrod::mono exterior $algmon]} {
		set edeg 0
	    }

	    Section "Working on C[expr {$s+1}] up to ideg=$ideg, edeg=$edeg" {
		# try to make us interruptible
		set ::steenrod::_progvarname ::yacop::progVar
		yacop::interruptible {
		    my Extend-line $s $ideg $edeg
		}
	    }
	}
    }

    method isComplete {sdeg ideg} {
	set last [GetLastIdeg $sdeg]
	expr {$last >= $ideg ? "1" : "0"}
    }

    method Extend-line {s ideg edeg} {

	foreach {vname inc} {prev -1 curr 0 next +1} {
	    set s$vname [expr {$s + $inc}]
	}

	set istart [set estart 0]
	if {[set lastideg [GetLastIdeg $snext]] >= 0} {
	    set istart [expr {$lastideg+1}]
	    StatusMsg "Last completed internal degree was $lastideg"
	    if {$istart > $ideg} return
	    if {($istart >= $ideg) && ($estart > $snext)} return
	}

        my db progress $::yacop::dbprogsteps yacop::ProgressHandler

	foreach suff {prev curr next} {
	    set swork [set s$suff]
	    Section "Reading generators for C$swork" {
		set genlist($suff) [GetGenlist $swork]
		GFR setGenlist $suff $genlist($suff)
		StatusMsg "[llength $genlist($suff)] generators read"
	    }
	}

	Section "Beginning with the computation" {

	    Section "Reading d$scurr" {
		GFR fillMonomap curr $scurr
	    }

	    Section "Reading d$snext" {
		GFR fillMonomap next $snext
	    }

	    my db transaction {

		set lastflush [clock seconds]
		set i $istart
		for {} {$i <= $ideg} {incr i} {
		    set e [expr {($i == $istart) ? $estart : 0}]
		    for {} {$e <= $edeg} {incr e} {

			yacop::ProgressHandler

			yacop::timer start

			GFR setTridegree $s $i $e
			set prof [GFR setmaxprofile $profmode]

			yacop::logvars s i e prof

			foreach {ngens ndiffs} [GFR resolve] break
			set cputime [yacop::timer stop]
			set numgens [llength $ngens]

			unset -nocomplain sdeginfo
			foreach newgen $ngens {
			    foreach {nid nsdeg nideg nedeg} $newgen break
			    incr sdeginfo($nsdeg)
			}

			yacop::logvars cputime numgens
			if {$numgens} {
			    set plurals [expr {($numgens>1) ? "s" : ""}]
			    set numgensdisp {}
			    foreach sdg [lsort -unique -integer [array names sdeginfo]] {
				lappend numgensdisp $sdeginfo($sdg)
			    }
			    set sectitle "$snext/$i/$e found [join $numgensdisp +] new generator$plurals"
			    if {$cputime >= 0} {
				append sectitle " in $cputime seconds"
			    }
			    Section $sectitle {
				#puts ngens=$ngens,ndiffs=$ndiffs
				#NewGenerators $snext $i $e $ngens $ndiffs
				foreach newgen $ngens ply $ndiffs {
				    foreach {nid nsdeg nideg nedeg} $newgen break
				    #puts "nid=$nid, nsdeg=$nsdeg, nideg=$nideg, nedeg=$nedeg\n  -> $ply"
				    if {[set gli [GetLastIdeg $nsdeg]] >= $nideg} {
					error "found new generator in (s,i)=($nsdeg,$nideg) but resolution claims to be complete up to internal degree $gli"
				    }
				    Generator add $prime $algmon $nid $nsdeg $nideg $nedeg $ply
				}
			    }
			}

			if 0 {
			    if {$numgens || $cputime >= 0.1} {
				set tdim [expr {$i-$s}]
				$sqlres timespent_insert $tdim $cputime
			    }
			}

			if {[clock seconds] > 10 + $lastflush} {
			    set now [clock format [clock seconds] -format "%d/%m/%Y %H:%M:%S"]
			    Section "setting checkpoint at $snext/$i/$e on $now" {
				my db eval {
				    commit;
				    begin
				}
				set lastflush [clock seconds]
			    }
			}
		    }

		    SetLastIdeg $snext $i

		}
	    }
	    yacop::logdbg "line $s finished"
	}
    }

    method lift {sdeg ideg edeg vectors} {
	puts "lifting $vectors in degree ($sdeg,$ideg,$edeg)"

	set scurr $sdeg
	set snext [expr {1+$sdeg}]

	set genlist [GetGenlist $scurr]

	foreach ename {Cfull Ccurr Cnext} \
	    sdg [list $sdeg $sdeg [expr {1+$sdeg}]] {
		steenrod::enumerator $ename -algebra $algmon -prime $prime \
		    -genlist [GetGenlist $sdg]
		$ename configure -ideg $ideg -edeg $edeg
		puts "basis / $ename:\n   [$ename basis]"
	    }

	Section "Reading d$snext" {
	    GFR fillMonomap next $snext
	}

	yacop::timer start

	GFR setTridegree $sdeg $ideg $edeg
	set prof [GFR setmaxprofile $profmode]
	set prof {0 0 {} 0}

	Cfull configure -profile {}
	Ccurr configure -profile $prof
	Cnext configure -profile $prof
	Ccurr sigreset
	Cnext sigreset

	set tolift [steenrod::matrix create [llength $vectors] [Cfull dim]]
	set r -1
	set ids {}
	foreach v $vectors {
	    lappend ids [incr r]
	    set phi($r) {}
	    steenrod::poly foreach $v m {
		set c [Cfull seqno $m]
		lset tolift $r $c \
		    [expr {([lindex $tolift $r $c]+[lindex $m 0])%$prime}]
	    }
	}
	puts tolift=$tolift

	while on {

	    Ccurr configure -signature [Cnext cget -signature]

	    puts "signature [Cnext cget -signature] / $prof"
	    foreach v {Ccurr Cnext} {
		puts "$v: [$v basis]"
	    }

	    # extract terms of this signature:
	    set seqmap [Cfull seqno Ccurr]
	    set submat [steenrod::matrix extract cols $tolift $seqmap]

	    puts submat=\n[join $submat \n]

	    # compute relevant part of matrix DSTcurr -> DSTprev
	    set mdsn [steenrod::ComputeMatrix Cnext mmnext Ccurr]

	    puts mdsn=\n[join $mdsn \n]

	    # compute lift
	    set lft [steenrod::matrix liftvar $prime mdsn submat]
	    unset mdsn

	    puts lft=$lft,submat=$submat

	    if {![steenrod::matrix iszero $submat]} {
		error "internal error: chosen subalgebra probably too big"
	    }
	    set cnt 0
	    set corrections {}
	    foreach id $ids {
		# TODO: use something better than "lindex" here!
		set preim [lindex [steenrod::matrix extract row $lft $cnt] 0]
		lappend corrections [set aux [Cnext decode $preim]]
		#puts phi($id)+=$aux
		steenrod::poly varappend phi($id) $aux
		incr cnt
	    }

	    # update tolift
	    steenrod::matrix addto tolift \
		[steenrod::ComputeImage mmnext Cfull $corrections] -1 $prime

	    if {![Ccurr signext] || ![Cnext signext]} break
	}

	if {![steenrod::matrix iszero $tolift]} {
	    error "internal error: lift not correct"
	}

	parray phi

	array get phi
    }

}

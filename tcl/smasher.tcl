#
# Smash product resolutions
#
# Copyright (C) 2009-2018 Christian Nassau <nassau@nullhomotopie.de>
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License version 2 as
# published by the Free Software Foundation.
#


oo::class create yacop::sagemodule {
    variable rescfg db actRMap diffMap
    constructor {rcfg dbcmd} {
        array set rescfg $rcfg
        set db $dbcmd

        my db eval {

            create temporary table if not exists
            sagemod_gens(rowid integer primary key,
                         sagename text unique,
                         sdeg integer,
                         ideg integer,
                         edeg integer);

            create temporary table if not exists
            sagemod_ops(type text,
                        op text,
                        srcgen integer,
                        result text);

        }

    }
    method db {subcmd args} {
        uplevel 1 [list $db $subcmd] $args
    }

    method addModuleGens {modgens} {
        # insert new generators into table
        set mcnt -1
        foreach ginfo $modgens {
            foreach {name degs} $ginfo break
            set gnum($name) [incr mcnt]
            set gdegs($name) $degs
        }
        my db eval {select sagename from sagemod_gens} {
            unset -nocomplain gdegs($sagename)
        }
        foreach {g degs} [array get gdegs] {
            dict with degs {
                my db eval {
                    insert into sagemod_gens(sagename,sdeg,ideg,edeg)
                    values($g,$s,$i,$e)
                }
            }
        }
        # identify missing information
        set todo(diff) {}
        my db eval {
            select sagename from sagemod_gens
            where rowid not in (select srcgen from sagemod_ops where type = 'diff')
        } {
            lappend todo(diff) $gnum($sagename)
        }

        A configure -genlist {0} ;# a single generator in dim 0
        unset -nocomplain aux
        if {$rescfg(viewtype) eq "even"} {
            set opsym Sq
        } else {
            set opsym Q
        }
        set p $rescfg(prime)
        set adict {}
        foreach newgen [array names gdegs] {
            set oplist {}
            set num $gnum($newgen)
            my db eval {
                select distinct gt.ideg-gs.ideg as i, gt.edeg-gs.edeg as e
                from sagemod_gens as gs, sagemod_gens as gt
                where gs.sagename = $newgen and gt.sdeg = gs.sdeg
                and i >= 0 and e >= 0
            } {
                A configure -ideg $i -edeg $e
                foreach m [A basis] {
                    lappend oplist (\"$m\",[yacop::sage::sagepoly $opsym false $p [list $m]])
                }
            }
            lappend adict $num:\[[join $oplist ,]\]
        }
        set todo(actR) [array get aux]
        return [format {{"diff":[%s],"actR":{%s}}} [join $todo(diff) ,] [join $adict ,]]
    }

    method addDiff {stuff} {
        #puts df=$stuff

        array set name2id [my db eval {
            select sagename,rowid from sagemod_gens
        }]

        foreach {gen diff} $stuff {
            set targ {}
            foreach {cf tg} $diff {
                lappend targ $cf $name2id($tg)
            }
            set sgen $name2id($gen)
            my db eval {
                insert into sagemod_ops(type,op,srcgen,result)
                values('diff',NULL,$sgen,$targ)
            }
        }
    }
    method addActionR {stuff} {
        #puts ar=$stuff
        array set name2id [my db eval {
            select sagename,rowid from sagemod_gens
        }]
        foreach {gen opspec} $stuff {
            set sgen $name2id($gen)
            foreach {op diff} $opspec {
                set targ {}
                foreach {cf tg} $diff {
                    lappend targ $cf $name2id($tg)
                }
                my db eval {
                    insert into sagemod_ops(type,op,srcgen,result)
                    values('actR',$op,$sgen,$targ)
                }
            }
        }
    }
    method generators {region} {
        set res {}
        my db eval {
            select sagename as name, sdeg, ideg, edeg from sagemod_gens
        } vals {
            unset -nocomplain vals(*)
            lappend res [array get vals]
        }
        return $res
    }
    method init {} {
        steenrod::monomap [set actRMap [namespace current]::actR]
        my db eval {
            select op,srcgen,result from sagemod_ops
            where type = 'actR'
        } {
            lset op end $srcgen
            $actRMap set $op $result
        }
        #puts actRMap=[$actRMap list]
        unset -nocomplain diffMap
        my db eval {
            select srcgen,result from sagemod_ops
            where type = 'diff'
        } {
            set diffMap($srcgen) $result
        }
    }
    method actR {gen op} {
        array set res {}
        set p $rescfg(prime)
        steenrod::poly foreach $op mono {
            lset mono end $gen
            foreach {cf tar} [$actRMap get $mono] {
                incr res($tar) [expr {$cf*[steenrod::mono coeff $mono]}]
            }
        }
        set rval {}
        foreach {key val} [array get res] {
            if {[set val [expr {$val % $p}]]} {
                lappend rval $val $key
            }
        }
        return $rval
    }
    method diff {gen} {
        return $diffMap($gen)
    }
}



oo::class create yacop::smashres {

    variable db res rescfg module debug errorCallback

    constructor {resolution modulename modcmd {errorcb barf} {filename :memory:}} {
        set res $resolution
        set modname $modulename
        set module $modcmd
	set debug 0
	set errorCallback $errorcb

        yacop::sqlite [set db [namespace current]::db] $filename

        array set rescfg [$res db eval {
            select key,value from yacop_cfg
        }]

        if {$rescfg(viewtype) eq "even"} {
	    set NEXPR "(ideg/2-sdeg)"
            #proc i2n {sdeg ideg} {expr {($ideg/2)-$sdeg}}
            #proc n2i {sdeg ndeg} {expr {2*($ndeg+$sdeg)}}
        } else {
            #proc i2n {sdeg ideg} {expr {$ideg-$sdeg}}
            #proc n2i {sdeg ndeg} {expr {$ndeg+$sdeg}}
	    set NEXPR "(ideg-sdeg)"
        }
        #my db function i2n [namespace current]::i2n
        #my db function n2i [namespace current]::n2i


        my db eval [subst {
            create table if not exists yacop_cfg
            (key text unique, value text);

            insert or ignore into yacop_cfg(key,value)
            values('type','module_smash_gfr');
            insert or ignore into yacop_cfg(key,value)
            values('module',:modname);

            create table if not exists
            module_generators(rowid integer primary key,
                              sagename text unique,
                              sdeg integer,
                              ideg integer,
                              edeg integer);

            create table if not exists
            smash_generators(rowid integer primary key,
                             resgen integer,
                             modgen integer,
                             sdeg integer,
                             ideg integer,
                             edeg integer,
                             ebasid integer /* unique for given s,i,e */,
                             basid integer  /* unique for given s,i */,
			     /* the status flag can be one of the following:
			     --   I(dle)         the generator is known
			     --   A(ctive)       we want to compute the differentials
			     --   D(one)         we have the differentials
			     --   H(omology)     we have computed the homology in this box
			     */
                             status char);

            create unique index if not exists smash_generatorsIdx1
            on smash_generators(resgen,modgen);

            create unique index if not exists smash_generatorsIdx2
            on smash_generators(sdeg,ideg,edeg,ebasid);

            create unique index if not exists smash_generatorsIdx3
            on smash_generators(sdeg,ideg,basid);

            create trigger if not exists smash_generators_mkbasid
            after insert on smash_generators when new.basid is null
            begin
            update smash_generators set basid = (select count(*)-1 from smash_generators
                                                     where sdeg=new.sdeg and ideg=new.ideg)
            where rowid=new.rowid;
            end;

            create table if not exists
            smash_fragments(rowid integer primary key,
                            /* this table contains only differentials
                            .  and Pts actions - it is not a complete
                            .  description of the smash product differential */
                            srcgen integer not NULL,
                            targen integer not NULL,
                            opideg integer not NULL,
			    opedeg integer not NULL,
                            format text not NULL,
                            data text not NULL);

            create table if not exists
            smash_boxes(rowid integer primary key,
                        sdeg integer,
                        ideg integer,
                        edeg integer,
                        matrix text,
                        cycles text,
                        boundaries text,
                        homology text);

            create unique index if not exists
            smash_boxes_idx1 on smash_boxes(sdeg,ideg,edeg);

            create table if not exists
            homology_gendata(rowid integer primary key,
                             boxid integer,
                             ebasid integer /* unique for given s,i,e */,
                             basid integer  /* unique for given s,i */);

            create trigger if not exists homology_gendata_mkbasid
            after insert on homology_gendata when new.basid is null
            begin
            update homology_gendata set basid = (select count(*)-1 from homology_gendata
                                                 join smash_boxes as b on boxid=b.rowid
                                                 join smash_boxes as bn on new.boxid=bn.rowid
                                                 where b.sdeg=bn.sdeg and b.ideg=bn.ideg)
            where rowid=new.rowid;
            end;

            create unique index if not exists homology_gendata_idx1
            on homology_gendata(boxid,ebasid);

            create view if not exists homology_generators as
            select h.rowid as rowid, b.sdeg as sdeg, b.ideg as ideg, b.edeg as edeg,
	    $NEXPR as ndeg,
            h.basid as basid, h.ebasid as ebasid
            from homology_gendata as h join smash_boxes as b on h.boxid=b.rowid;

	    /* oplist contains the Pts (and the unit) that are chart-relevant */
	    create table oplist(rowid integer primary key,
				pts text,
				op text,
				opideg integer,
				opedeg integer);

	    create table if not exists
	    homology_fragment_request(boxid integer references smash_boxes(rowid),
				      oprowid integer references oplist(rowid));
	    create unique index if not exists idx_homology_fragment_request
	    on homology_fragment_request(boxid,oprowid);

            create table if not exists
            homology_fragments(srcgen integer,
                               targen integer,
                               opideg integer,
			       opedeg integer,
                               format text,
                               data text);

            create index if not exists
            homology_fragments_idx1 on homology_fragments(srcgen,opideg);

            create table if not exists chart_viewtypes
            (name text unique, desc text, code text);

        }]

        foreach {key value} [$res db eval {
            select key,value from yacop_cfg
            where key in ('prime','algebra')
        }] {
            my db eval {
                insert or ignore into yacop_cfg(key,value) values($key,$value)
            }
        }
        array set mycfg [my db eval {
            select key,value from yacop_cfg
        }]

        if {$mycfg(prime) != $rescfg(prime)
            || $mycfg(algebra) ne $rescfg(algebra)} {
            error "prime/algebra mismatch"
        }
        if {$mycfg(module) != $modulename} {
            error "file has modulename '$mycfg(module)' but module is '$modulename'"
        }

        foreach {major minor} {
            smash-product even
            smash-product odd
            homology even
            homology odd
        } {
            if {[regexp even $minor] && ($rescfg(prime) != 2 || [lindex $rescfg(algebra) 0] != 0)} continue
            if {$rescfg(prime) != 2} {
                set name $major
            } else {
                set name "$major ($minor)"
            }
            set desc $name
            array set majorcode {
                smash-product {
                    create temporary view chart_generators as
                    select g.rowid, g.sdeg, g.IDEG-g.sdeg as ndeg, g.ideg, g.edeg, g.basid
		    from smash_generators g
		    join smash_boxes b on b.sdeg = g.sdeg and b.ideg = g.ideg and b.edeg = g.edeg
		    where g.status in ('D', 'H') and not b.homology is null ;
                    create temporary view chart_fragments as
		    select * from smash_fragments as sf join smash_generators as sg on sf.targen=sg.rowid
		    where sg.status in ('D', 'H');
                }
                homology {
                    drop view if exists chart_generators_aux;
                    create temporary view chart_generators_aux as
                    select h.rowid,b.sdeg,b.ideg,b.edeg,h.basid from homology_gendata as h
                    join smash_boxes as b on h.boxid=b.rowid;
                    create temporary view chart_generators as
                    select rowid, sdeg, IDEG-sdeg as ndeg, ideg, edeg, basid from chart_generators_aux;
                    create temporary view chart_fragments as select * from homology_fragments;
                }
            }
            if {[regexp even $minor]} {
                set map {IDEG ideg/2}
            } else {
                set map {IDEG ideg}
            }
            set code [string map $map $majorcode($major)]
            my db eval {
                insert or replace into chart_viewtypes(name,desc,code) values($name,$desc,$code);
            }
        }

        my db eval {
            insert or ignore into yacop_cfg(key,value)
            values('viewtype',(select name from chart_viewtypes
                               where name like '%homology%' order by name limit 1))
        }
        my db eval [my db onecolumn {select code from chart_viewtypes
            where name=(select value from yacop_cfg where key='viewtype')}]

	my MakeOplist

        steenrod::enumerator A -prime $mycfg(prime) -algebra [steenrod::algebra tomono $mycfg(algebra)]
    }

    method db {args} {
        if {[llength $args] == 0} {
            return $db
        }
        uplevel 1 [list $db] $args
    }
    method module {subcmd args} {
        uplevel 1 [list $module $subcmd] $args
    }

    method expand-region {region} {
        array set r $region
        foreach {nm off} {
            smax +1 smin -1
        } {
            if {[info exists r($nm)]} {
                incr r($nm) $off
            }
        }
        array get r
    }

    method dbgprint {msg {code {}}} {
	if 0 {
	    puts $msg
	    if {$code ne ""} { uplevel 1 $code }
	}
    }

    method tabledump {sql} {
        set fmt "|"
        my db eval $sql h {
            if {$fmt eq "|"} {
            foreach x $h(*) {
                append fmt " %9s |"
            }
            puts [format $fmt {*}$h(*)]
            }
            set row {}
            foreach x $h(*) { lappend row $h($x) }
            puts [format $fmt {*}$row]
        }
    }

    method update_module {modrange} {
        my db transaction {
            foreach geninfo [my module generators $modrange] {
                dict with geninfo {
                    my db eval {
                        insert or ignore into
                        module_generators(sagename,sdeg,ideg,edeg)
                        values($name,$sdeg,$ideg,$edeg)
                    }
                }
            }
        }
        my dbgprint "module generators:" {
            my tabledump {
            select sdeg, ideg, edeg, count(*) dim
            from module_generators
            group by sdeg, ideg, edeg
            order by sdeg, ideg, edeg
            }
        }
    }

    method new-smashgen {rsdeg rideg redeg msdeg mideg medeg resgen modgen} {
        set ebasid [my db onecolumn {
            select count(*) from smash_generators
            where sdeg=$rsdeg+$msdeg
            and ideg=$rideg+$mideg
            and edeg=$redeg+$medeg
        }]
        my db eval {
            insert or ignore into smash_generators
            (resgen,modgen,sdeg,ideg,edeg,ebasid,status)
            values
            ($resgen,$modgen,$rsdeg+$msdeg,$rideg+$mideg,$redeg+$medeg,$ebasid,'I')
        }
    }

    method update_smash_boxes {} {
	# assumption: resolution or module has been extended
	# now create new smash_boxes for the new generators
	# TODO: allow restrictions if only part of the resolution needs to be used

	namespace path [list {*}[namespace path] ::yacop::sectionizer]
	set ::steenrod::_progvarname ::yacop::progVar
	yacop::interruptible {
	    my db progress $::yacop::dbprogsteps yacop::ProgressHandler
	    my db transaction {
		Section "Updating smash product basis" {
		    set lastflush [clock seconds]
		    $res db eval {
			select rowid as resgen, sdeg as rsdeg, ideg as rideg, edeg as redeg
			from generators order by sdeg,ideg,edeg
		    } {
			my db eval {
			    select rowid as modgen, sdeg as msdeg, ideg as mideg, edeg as medeg
			    from module_generators
			    where not exists( select rowid from smash_generators
					      where resgen=:resgen and modgen=:modgen )
			} {
			    yacop::ProgressHandler
			    my new-smashgen $rsdeg $rideg $redeg $msdeg $mideg $medeg $resgen $modgen
			    my db eval {
				select rowid as gid, sdeg,ideg,edeg from smash_generators
				where resgen=$resgen and modgen=$modgen
			    } break
			    my db eval {
				insert or ignore into smash_boxes(sdeg,ideg,edeg)
				values($sdeg,$ideg,$edeg)
			    }
			    set msg "Setting checkpoint at $sdeg/$ideg/$edeg"
			    if {[clock seconds]>$lastflush+10} {
				Section $msg {
				    my db eval "commit;begin"
				    set lastflush [clock seconds]
				}
			    }
			}
		    }
		}
	    }
	}
	my dbgprint "smash boxes and #generators" {
	    my tabledump {
		select b.rowid, g.sdeg, g.ideg, g.edeg, count(*) as dim, g.havediff
		from smash_generators g
		join smash_boxes b on g.sdeg = b.sdeg and g.ideg = b.ideg and g.edeg = b.edeg
		group by b.rowid, g.sdeg, g.ideg, g.edeg, g.havediff
		order by b.rowid, g.sdeg, g.ideg, g.edeg, g.havediff
	    }
	}
    }

    method activate_smash_generators {region} {
	# we also activate generators of one higher homological degree
	set conds [my region2sql $region "" smaxoff 1 nminoff -1]
	if {$rescfg(viewtype) eq "even"} {
	    lappend map ndeg (ideg/2-sdeg)
	    lappend map tdeg (ideg/2)
	} else {
	    lappend map ndeg (ideg-sdeg)
	    lappend map tdeg ideg
	}
	set conds [string map $map $conds]
	#puts activate-sg:region=$region,conds=$conds
	my db transaction {
	    set sql [subst {
	    update smash_generators
	    set status = 'A'
	    where status = 'I' and $conds
	    }]
	    #puts region=$region,sql=$sql
	    my db eval $sql
	}
    }

    method update_smash_fragments {} {
	# go through all eligible smash_generators that have no differential
	# and compute the corresponding fragments
	namespace path [list {*}[namespace path] ::yacop::sectionizer]
	set ::steenrod::_progvarname ::yacop::progVar
	yacop::interruptible {
	    my db progress $::yacop::dbprogsteps yacop::ProgressHandler
	    my db transaction {
		Section "Updating smash fragment table" {
		    set lastflush [clock seconds]
		    my db eval {
			select g.rowid as gid, g.sdeg, g.ideg, g.edeg
			from smash_generators g
			where g.status = 'A'
			order by g.resgen, g.sdeg, g.ideg, g.edeg
		    } {
			my MakeSmashFragments $gid
			set msg "Setting checkpoint at $sdeg/$ideg/$edeg"
			if {[clock seconds]>$lastflush+10} {
			    Section $msg {
				my db eval "commit;begin"
				set lastflush [clock seconds]
			    }
			}
		    }
		}
	    }
	}
	if {[info exists ::env(YACOP_DOUBLECHECK)] && $::env(YACOP_DOUBLECHECK)} {
	    my CheckSmashFragments
	}
    }

    method region2sql {region prefix args} {
	set cond {}
	foreach {v val} $region {
	    if {[dict exists $args ${v}off]} {
		incr val [dict get $args ${v}off]
	    }
	    set vv [string index $v 0]
	    switch -regexp $v {
		min {
		    lappend cond "${prefix}${vv}deg>=$val"
		}
		max {
		    lappend cond "${prefix}${vv}deg<=$val"
		}
		default {
		    lappend cond "${prefix}${vv}deg=$val"
		}
	    }
	}
	set cond [join $cond " and "]
	return $cond
    }

    method update_homology {region tfactor} {
	# go through all smash_boxes in the given region and compute the homology

	set cond [my region2sql $region x]

	# we assume (and do not check) that all required boxes have already been computed
	# TODO: decide whether an extra check is advised

	set sql [subst {
	    select
	    ccurr.rowid as boxrowid,
	    ccurr.sdeg as xsdeg,
	    (ccurr.ideg/:tfactor) as xtdeg,
	    (ccurr.ideg/:tfactor)-ccurr.sdeg as xndeg,
	    ccurr.edeg as xedeg
	    from smash_boxes ccurr
	    left join smash_boxes cnext on cnext.sdeg=ccurr.sdeg+1 and cnext.ideg=ccurr.ideg and cnext.edeg=ccurr.edeg
	    left join smash_boxes cprev on cprev.sdeg=ccurr.sdeg-1 and cprev.ideg=ccurr.ideg and cprev.edeg=ccurr.edeg
	    where $cond and ccurr.homology is null
	    group by ccurr.rowid, cnext.rowid, cprev.rowid
	    order by ccurr.sdeg, ccurr.ideg, ccurr.edeg
	}]

	my dbgprint "sql=$sql"

	namespace path [list {*}[namespace path] ::yacop::sectionizer]
	set ::steenrod::_progvarname ::yacop::progVar
	yacop::interruptible {
	    my db progress $::yacop::dbprogsteps yacop::ProgressHandler
	    my db transaction {
		Section "Updating homology" {
		    set lastflush [clock seconds]
		    my db eval $sql {
			my MakeHomology $boxrowid
			set msg "Setting checkpoint at $xsdeg/$xtdeg/$xedeg"
			if {[clock seconds]>$lastflush+10} {
			    Section $msg {
				my db eval "commit;begin"
				set lastflush [clock seconds]
			    }
			}
		    }
		}
	    }
	}
    }

    method MakeOplist {} {
        # we're only going to compute the portion of the differential
        # in the smash product which is chart- and homology-relevant.
        # these are the (indecomposable) pts in the algebra and the unit
	set op {1 0 {} 0}
	set opideg 0
	set opedeg 0
	set pts ""
	my db eval {
	    insert into oplist(pts,op,opideg,opedeg)
	    values(:pts,:op,:opideg,:opedeg);
	}
        set p $rescfg(prime)
        set powers [steenrod::prime $p powers]
        foreach pts [steenrod::algebra ptslist $rescfg(algebra) [expr {[llength $powers]-1}]] {
            switch -- [lindex $pts 0],[lindex $pts 1] {
                P,1 {
                    set x [string repeat "0 " [lindex $pts 1]]
                    lappend x [lindex $powers [lindex $pts 2]]
		    set op [list 1 0 [lrange $x 1 end] 0]
		    set opedeg 0
                }
                Q,0 {
		    set op [list 1 [expr {1<<[lindex $pts 1]}] {} 0]
		    set opedeg 1
                }
		default {
		    continue
		}
            }
	    set opideg [steenrod::mono degree $p $op]
	    my db eval {
		insert into oplist(pts,op,opideg,opedeg)
		values(:pts,:op,:opideg,:opedeg);
	    }
        }
    }

    method CheckSmashFragments {} {
	# sanity check, corresponding to d^2 = 0
        set p $rescfg(prime)
	my db eval {
	    /* genfrags = sources of differentials + status flag that indicates
	    .. whether all targets have a completely computed differential */
	    with genfrags(srcgen,status) as
	    (select f.srcgen, max(case g.status when 'I' then 1 else 0 end) as status
	     from smash_fragments f join smash_generators g on f.targen = g.rowid
	     group by f.srcgen)
	    select (dn.opideg + dc.opideg) as dg, dn.srcgen, dc.targen,
	    group_concat(dn.targen) as steps,
	    sum(opcoeff(dn.data) * opcoeff(dc.data)) % :p as cf
	    from genfrags gf
	    join smash_fragments dn on dn.srcgen = gf.srcgen
	    join smash_fragments dc on dc.srcgen = dn.targen
	    where gf.status = 0 and (dn.opideg=0 or dc.opideg=0)
	    group by dn.srcgen, dc.targen, dg
	    having cf != 0
	} {
	    puts "ERROR(CheckSmashFragments): $srcgen -> $steps -> $targen / coefficient $cf"
	}
    }

    method opfilter {op pts data monovar bdy} {
	upvar 1 $monovar mono
	#puts op=$op,pts=$pts,data=$data
	if {$pts eq ""} {
	    # op = id
	    foreach mono $data {
		uplevel 1 $bdy
	    }
	} elseif {[lindex $pts 0] eq "Q"} {
	    foreach mono $data {
		set ext [lindex $mono 1]
		if {1&$ext} {
		    lset mono 1 [expr {1^$ext}]
		    uplevel 1 $bdy
		}
	    }
	} else {
	    set opow [lindex $op 2 0]
	    foreach mono $data {
		set red [lindex $mono 2 0]
		if {$red ne "" && $red >= $opow} {
		    lset mono 2 0 [expr {$red-$opow}]
		    if {[lindex $mono 2] eq "0"} {lset mono 2 {}} ;# FIXME: hack alert
		    uplevel 1 $bdy
		}
	    }
	}
    }

    method find-modgen {gname sdeg ideg edeg} {
	set ans [my db eval {
	    select rowid from module_generators where sagename=$gname
	}]
	if {$ans eq ""} {
	    my db eval {
		insert into module_generators(sagename, sdeg, ideg, edeg)
		values(:gname,:sdeg,:ideg,:edeg)
	    }
	    set ans [my db last_insert_rowid]
	}
	return $ans
    }

    method find-smashgen {resgen modgen} {
	set ans [my db eval {
	    select rowid from smash_generators
	    where resgen=:resgen and modgen=:modgen
	}]
	if {$ans eq ""} {
	    $res db eval {
		select sdeg as rsdeg, ideg as rideg, edeg as redeg from generators where rowid=:resgen
	    } break
	    my db eval {
		select sdeg as msdeg, ideg as mideg, edeg as medeg from module_generators where rowid=:modgen
	    } break
	    my new-smashgen $rsdeg $rideg $redeg $msdeg $mideg $medeg $resgen $modgen
	    set ans [my db last_insert_rowid]
	}
	return $ans
    }

    method MakeSmashFragments {genid} {

        set p $rescfg(prime)
	set oplist {}
	set ptslist {}
	set ptsdeglist {}
	my db eval {
	    select pts, op, opideg, opedeg from oplist order by opideg
	} {
	    lappend oplist $op
	    lappend ptslist $pts
	    lappend ptsdeglist $opideg
	}

        my db eval {
            update smash_generators set status='D' where rowid = $genid;
            select resgen, modgen, sdeg, ideg, edeg from smash_generators where rowid = $genid
        } break
        set mideg [my db onecolumn {select ideg from module_generators where rowid=$modgen}]

        # account for the internal differential on M, using d(m\land g) = dm\land g + ...
        foreach {cf gname} [$module diff $modgen] {
            #puts cf=$cf,tarmod=$gname
	    set sagegen [my find-modgen $gname [expr {$sdeg-1}] $ideg $edeg]
	    set dstid [my find-smashgen $targen $sagegen]
	    set cfunit [list [list $cf 0 {} 0]]
            my db eval {
                insert into
                smash_fragments(srcgen,targen,opideg,opedeg,format,data)
                values(:genid,:dstid,0,0,'tcl',:cfunit);
            }
        }

        # go through all resolution fragments "m smash a*$targen" that originate on resgen,
        # then for all op from oplist create a corresponding smash
        # fragment "op * (chi(a/op)*m smash $targen)"
        $res db eval {
            select targen,data,opideg,opedeg from fragview where srcgen = $resgen
        } {
            foreach pts $ptslist op $oplist ptsdeg $ptsdeglist {

		#set debug [expr {$pts eq ""}]
		if {$debug} { puts "$resgen -> $data * $targen" }

		if {$ptsdeg>$opideg} continue

		set shifted {}
 		my opfilter $op $pts $data mono {
		    lappend shifted $mono
		}

		#puts data=$data,op=$op:\nshifted=$shifted

		if {0==[llength $shifted]} continue

		set sagename [my db onecolumn {select sagename from module_generators where rowid=$modgen}]
		set action [$module actR $sagename $shifted]

		if 0 {
		    with a' = op, shifted = a'' we have a summand of "m\land data*g", as in

		    .    m \land ag = \sum (-1)^{|a|*|m|} a' * (chi(a'')m \land g)
		}

		set sign [expr { ($mideg & $opideg & 1) ? -1 : 1 }]

		if {0 && ($ideg & 1)} {
		    # our resolution is linear in the ungraded sense. flip a sign to make it
		    # obey the Koszul sign rule with a differential of degree 1
		    set sign [expr {-$sign}]
		}

		if {$debug} {
		    puts " $data/$op =  $shifted"
		    puts " [list $module actR $sagename $shifted]"
		    puts " right action on $modgen: $action"
		    puts " sign = $sign"
		}

		foreach {cf gname} $action {
		    set sagegen [my find-modgen $gname [expr {$sdeg-1}] $ideg $edeg]
		    set op2 $op
		    lset op2 0 [expr {$sign*$cf}]
		    set op2l [list $op2]
		    set smashgen [my find-smashgen $targen $sagegen]
		    my db eval {
			insert into
			smash_fragments(srcgen,targen,opideg,opedeg,format,data)
			values($genid,$smashgen,$ptsdeg,0,'tcl',$op2l); -- fixme: opedeg correct?
		    }

		}
	    }
	}
    }

    method setDebug {newval} {
	set debug [expr {$newval ? 1 : 0}]
    }

    method MakeHomology {boxid} {
        set p $rescfg(prime)
        my db eval {
            select sdeg,edeg,ideg,cycles isnull as needc, boundaries isnull as needb
            from smash_boxes where rowid=$boxid
        } break
        if {$needc} {my MakeMatrix $sdeg $ideg $edeg}
        if {$needb} {my MakeMatrix [expr {$sdeg+1}] $ideg $edeg}
        my db eval {
            select cycles, boundaries from smash_boxes where rowid=$boxid
        } break
        steenrod::matrix quot $p cycles $boundaries
        my db eval {
            update smash_boxes set homology=$cycles where rowid=$boxid
        }
	if {$debug} { my matlog cycles "homology ($sdeg,$ideg,$edeg)" }
        if {0 == [llength $cycles]} return

	# REPEAT AFTER ME: DO NOT LOOP OVER MATRICES, THEY DO NOT HAVE WELL-DEFINED DIMENSIONS IN THE STRING REPRESENTATION

        set idx -1
        foreach row $cycles {
            incr idx
            my db eval {
                insert into homology_gendata(boxid,ebasid)
                values(:boxid,:idx);
            }
            #set hlgyrowid($idx) [my db last_insert_rowid]
        }
	# TODO: restrict this to a reasonable range (e.g., do not expect
	# hi-multiplications that originate from (very) negative dimensions)
	my db eval {
	    insert into homology_fragment_request(boxid,oprowid)
	    select :boxid,rowid from oplist;
	}
    }

    method update_homology_fragments {} {
	# compute all homology fragments that have now become computable
	# these could also be connections *into* our new boxes from boxes that had
	# been computed in an earlier run

	my db transaction {
	    my db eval {
		select req.rowid as reqid,
		src.rowid as boxid,
		src.sdeg, src.ideg, src.edeg,
		op.op, op.opideg, op.opedeg, op.pts
		from homology_fragment_request req
		join oplist op on op.rowid = req.oprowid
		join smash_boxes src on src.rowid = req.boxid
		join homology_gendata hgs on hgs.boxid = src.rowid and hgs.ebasid=0
		join smash_boxes dst
		on dst.sdeg = src.sdeg-1
		and dst.ideg = src.ideg-op.opideg
		and dst.edeg = src.edeg-op.opedeg
		join homology_gendata hgd on hgd.boxid = dst.rowid and hgd.ebasid=0
	    } {
		my MakeHomologyFragment $boxid $sdeg $ideg $edeg $pts $op $opideg $opedeg
		my db eval {
		    delete from homology_fragment_request where rowid=:reqid
		}
	    }
	}
    }

    method MakeHomologyFragment {boxid sdeg ideg edeg pts op opideg opedeg} {

        set p $rescfg(prime)
        my db eval {
            select rowid, ebasid,count(*) as srcdim from smash_generators
            where sdeg=:sdeg and ideg=:ideg and edeg=:edeg
        } {
            set bid2gid($ebasid) $rowid
        }

	set tardim [my db onecolumn {
	    select count(*) from smash_generators
	    where sdeg=:sdeg-1 and ideg=:ideg-:opideg and edeg=:edeg-:opedeg
	}]
	set mat [steenrod::matrix create $srcdim $tardim]
	set frags {}
        my db eval {
            select s.ebasid as srcbid, t.ebasid as tarbid,
	    f.opideg as opideg, f.data as data /* smash fragments don't need frag_decode */
            from smash_generators s
            join smash_fragments f on f.srcgen=s.rowid
            join smash_generators t on f.targen=t.rowid
            where s.sdeg=$sdeg and s.ideg=$ideg and s.edeg=$edeg
	    and f.opideg=:opideg /* we use that ops in oplist are uniquely specified by their opideg */
        } {
            set theop [lindex $data 0]
            set cf [lindex $theop 0]
            lappend frags $srcbid $tarbid $cf
        }
	foreach {r c v} $frags {
	    set val [lindex $mat $r $c]
	    set val [expr {($val+$v)%$p}]
	    lset mat $r $c $val
	}

	my db eval {
	    select rowid, ebasid from homology_gendata
	    where boxid=:boxid
	} {
	    set hlgyrowid($ebasid) $rowid
	}

	my db eval {
            select homology as cycles, homology as curhom from smash_boxes where rowid=$boxid
        } break
	set mat2 [steenrod::matrix multiply $p $cycles $mat]

	#puts "Computing fragments origination on the homology generators $curhom"

	# express rows of mat2 in terms of homology generators

	my db eval {
	    select homology, boundaries, rowid as tarboxid, count(*) as targetexists from smash_boxes
	    where sdeg=$sdeg-1 and ideg=$ideg-$opideg and edeg=$edeg-$opedeg
	} break

	if {!$targetexists} return

	set hdim [llength $homology]
	if {$hdim == 0} return

	if {$debug} {
	    my matlog mat2       "cycles to lift"
	    my matlog homology   "homology"
	    my matlog boundaries "boundaries"
	}

	set hcpy $homology
	lappend homology {*}$boundaries

	if {[llength $homology]} {
	    set lft [steenrod::matrix liftvar $p homology mat2]
	} else {
	    set lft [steenrod::matrix create {*}[steenrod::matrix dimensions $mat2]]
	}

	if {$debug} {
	    my matlog lft "lift"
	    my matlog mat2 "remainder"
	}

	set idx -1
	foreach row $curhom lftrow $lft matrow $mat2 {
	    #puts row=$row,lftrow=$lftrow,matrow=$matrow
	    incr idx
	    if {[steenrod::matrix iszero [list $matrow]]} {
		set cidx -1
		#puts lftrow=$lftrow,hdim=$hdim
		foreach c $lftrow {
		    if {[incr cidx] >= $hdim} break
		    if {0 == $c} continue
		    set srcgen $hlgyrowid($idx)
		    set targen [my db onecolumn {
			select rowid from homology_gendata
			where boxid = :tarboxid
			and ebasid=$cidx
		    }]
		    if {$targen eq ""} {
			puts "$op:sdeg=$sdeg-1 and ideg=$ideg-$deg and edeg=$edeg-$eoff and ebasid=$cidx"
			error "targen is empty"
		    }
		    lset op 0 $c
		    my db eval {
			insert into homology_fragments(srcgen,targen,format,data,opideg,opedeg)
			values($srcgen,$targen,'tcl',list($op),$opideg,:opedeg);
		    }
		}
	    } else {
		set errmsg [subst {
		    matrix did not reduce to zero:
		    (s,i,e) = ($sdeg,$ideg,$edeg)
		    op=$op
		    mat=$mat
		    cycles=$cycles
		    mat2=$mat2
		    homology=$homology
		    boundaries=$boundaries
		    lftrow=$lftrow
		    matrow=$matrow
		}]
		$errorCallback [format {{'s':%d,'i':%d,'e':%d}} $sdeg $ideg $edeg] $errmsg
		#error "internal error"
	    }
	}



    }

    method MakeMatrix {sdeg ideg edeg} {
        # create matrix (s,i,e) -> (s-1,i,e)
        set p $rescfg(prime)
        set srcboxid [my db eval {
            select rowid from smash_boxes where sdeg=$sdeg and ideg=$ideg and edeg=$edeg
        }]
        set tarboxid [my db eval {
            select rowid from smash_boxes where sdeg=$sdeg-1 and ideg=$ideg and edeg=$edeg
        }]
        set srcdim [my db onecolumn {
            select count(*) from smash_generators where sdeg=$sdeg and ideg=$ideg and edeg=$edeg
        }]
        set tardim [my db onecolumn {
            select count(*) from smash_generators where sdeg=$sdeg-1 and ideg=$ideg and edeg=$edeg
        }]
        set matrix [steenrod::matrix create $srcdim $tardim]
        my db eval {
            select rowid as srcid, ebasid as srcebasid from smash_generators
            where sdeg=$sdeg and ideg=$ideg and edeg=$edeg order by ebasid asc
        } {
            my db eval {
                select targen,data,sg.ebasid as tarebasid from smash_fragments
                join smash_generators as sg on sg.rowid = targen
                where srcgen=$srcid and opideg=0
            } {
                set cf [lindex $data 0 0]
                set ncf [expr {($cf+[lindex $matrix $srcebasid $tarebasid])%$p}]
                lset matrix $srcebasid $tarebasid $ncf
            }
        }
        my db eval {
            update smash_boxes set matrix=$matrix where rowid=$srcboxid
        }
	if {$debug} {
	    my matlog matrix "matrix ($sdeg,$ideg,$edeg)"
	}
        steenrod::matrix ortho $p matrix ker
	if {$debug} {
	    my matlog ker "kernel ($sdeg,$ideg,$edeg)"
	    my matlog matrix "boundaries ($sdeg,$ideg,$edeg)"
	}
        my db eval {
            update smash_boxes set cycles=$ker where rowid=$srcboxid
        }
        my db eval {
            update smash_boxes set boundaries=$matrix where rowid=$tarboxid
        }
    }

    method matlog {matvar desc} {
	upvar 1 $matvar m
	puts "MATRIX $desc\n[join $m \n]"
    }

    method sage_homology_class {cycle} {
        set p $rescfg(prime)

        foreach {cf mname resgen} $cycle {
            my db eval {
                select sg.ebasid as ebasid, sb.rowid as boxid from
                smash_generators as sg
                join module_generators as mg on mg.rowid = sg.modgen
                join smash_boxes as sb
                on sb.sdeg = sg.sdeg and sb.ideg = sg.ideg and sb.edeg = sg.edeg
                where sg.resgen=$resgen and mg.sagename=$mname
            } {
                lappend vals($boxid) $cf $ebasid
            }
        }

        set res {}
        foreach box [array names vals] {
            my db eval {
                select homology, boundaries from smash_boxes where rowid=$box
            } break

            set hdim [llength $homology]
            lappend homology {*}$boundaries

            foreach {r c} [steenrod::matrix dimension $homology] break
            set row [steenrod::matrix create 1 $c]

            #puts row=$row,vals=$vals($box),hom+bdr=$homology,hdim=$hdim

            foreach {cf idx} $vals($box) {
                set x [lindex $row 0 $idx]
                if {$x eq ""} {set x 0}
                set x [expr {($x+$cf)%$p}]
                lset row 0 $idx $x
            }

            if {[llength $homology]} {
                set lft [steenrod::matrix lift $p $homology row]
            } else {
                set lft [steenrod::matrix create {*}[steenrod::matrix dimensions $row]]
            }

            if {![steenrod::matrix iszero $row]} {
                error "vector didn't reduce to zero"
            }

            set cidx -1
            foreach c [lindex $lft 0] {
                if {[incr cidx] >= $hdim} break
                if {0 == $c} continue
                set targen [my db onecolumn {
                    select rowid from homology_gendata
                    where boxid=$box and ebasid=$cidx
                }]
                if {$targen eq ""} {
		    puts "$op:sdeg=$sdeg-1 and ideg=$ideg-$deg and edeg=$edeg-$eoff and ebasid=$cidx";
		    barf;
		    continue
		}
                lappend res "($c,$targen)"
            }
        }
        return "\[[join $res ,]\]"
    }
}

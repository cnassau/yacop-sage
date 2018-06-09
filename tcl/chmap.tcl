#
# Chain map computations
#
# Copyright (C) 2009 Christian Nassau <nassau@nullhomotopie.de>
#
#  $Id: chmap.tcl,v 1.6 2009/05/09 20:44:00 cn Exp $
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License version 2 as
# published by the Free Software Foundation.
#


oo::class create yacop::chainmap {
    
    variable db src dst cfg srccfg dstcfg
    
    constructor {srcres dstres algmap basecycle {filename :memory:}} {
        set src $srcres
        set dst $dstres

        array set srccfg [$src config]
        array set dstcfg [$dst config]
        set prime $srccfg(prime)
        
        # normalize basecycle which is a list "?coeff? ?id? ?coeff? ?id? ..."
        set basecycle [join $basecycle " "]

        array set srccfg [$src config]
        set cfg(viewtype) $srccfg(viewtype)

        #puts algmap=$algmap,basecycle=$basecycle

        yacop::sqlite [set db [namespace current]::db] $filename
        
	     namespace path [list {*}[namespace path] ::yacop::sectionizer]

        my db transaction {
            
            my db eval {
                create table if not exists yacop_cfg
                (key text unique, value text);
                
                insert or ignore into yacop_cfg(key,value)
                values('type','gfr_chainmap');
                
                create table if not exists generators
                (/* the generators we have computed */
                 rowid integer primary key);
 
                create table if not exists fragments
                (/* the summands of the chain map */
                 rowid integer primary key,
                 srcgen integer, /* rowid of source generator */
                 targen integer, /* rowid of target generator */
                 opideg integer, /* internal degree of this piece */
                 format text,    /* how data is encoded */
                 data text       /* the data */);
                
                create view if not exists fragview
                as select rowid,srcgen,targen,opideg,
                frag_decode(format,data) as data from fragments;
                
                create index if not exists fraglookupsrc
                on fragments(srcgen,targen);
                
                create index if not exists fraglookupdeg
                on fragments(opideg,targen);
            }

            array set cfg [my get-config]
            if {$basecycle eq "default"} {
                if {![info exists cfg(basecycle)]} {
                    error "basecycle not set in file \"$filename\""
                }
            } else {
                if {[info exists cfg(basecycle)] && $cfg(basecycle) ne $basecycle} {
                    error "basecycle mismatch: file \"$filename\" has >$cfg(basecycle)<, you gave >$basecycle<"
                }
                if {![info exists cfg(basecycle)]} {
                    my db eval {
                        insert or ignore into yacop_cfg(key,value)
                        values('basecycle',$basecycle);
                    }
                }
            }
            if {$algmap eq "default"} {
                if {![info exists cfg(algmap)]} {
                    error "algmap not set in file \"$filename\""
                }
            } else {
                if {[info exists cfg(algmap)] && $cfg(algmap) ne $algmap} {
                    error "algmap mismatch: file \"$filename\" has >$cfg(algmap)<, you gave >$algmap<"
                }
                if {![info exists cfg(algmap)]} {
                    my db eval {
                        insert or ignore into yacop_cfg(key,value)
                        values('algmap',$algmap);
                    }
                }
            }

            array set cfg [my get-config]
            
            foreach {cf id} $cfg(basecycle) {
                unset -nocomplain sdeg
                $src db eval {
                    select sdeg,ideg,edeg from generators
                    where rowid=$id
                } break
                lappend aux($sdeg,$ideg,$edeg) .
            }
            
            if {[llength [array names aux]] != 1} {
                error "cycle not homogeneous: lives in degrees [join [lsort [array names aux]] {, }]"
            }
            
            foreach v {sdeg ideg edeg} {
                set cfg($v) [set $v]
            }
            
            # insert basecycle if not already present
            set unit [$dst db onecolumn {
                select rowid from generators where sdeg = 0 and ideg = 0 and edeg = 0
            }]
            foreach {cf id} $cfg(basecycle) {
                if {0 == [my db eval {select count(*) from generators where rowid=$id}]} {
                    set opideg 0
                    switch -- $algmap {
                        psi {
                            set dalg [dict get [$dst algebra] algebra]
                            set x {}
                            set y {}
                            foreach exp [lindex $dalg 1] {
                               lappend x [expr {-($prime**$exp)}]
                               lappend y 20
                            }
                            set red [lindex $dalg 0]
                            set op [list $cf [expr {-1-$red}] $x $unit] 
                            set ideg [steenrod::mono degree $prime $op]
                            set ideg [expr {-($ideg-[steenrod::mono degree $prime {0 -1 -1 0}])}]
                            set cfg(ideg) $ideg
                            # replace last entry in negalg by "1"
                            lappend y 1
                            set y [lrange $y 1 end]
                            set cfg(negalg) [list 1 $red $y 0]
                        }
                        default { set op [list $cf 0 {} $unit] }
                    }
                    my db eval {
                        insert into fragments(srcgen,targen,opideg,format,data)
                        values($id,$unit,$opideg,'tcl',list($op))
                    }
                }
            }

            # declare all generators in earlier degrees to be done
            $src db eval {
                select rowid from generators where sdeg <= $sdeg
            } {
                my db eval {
                    insert or ignore into generators(rowid) values($rowid)
                }
            }
        } 
    }
    
    method get-config {} {
        my db eval {select key, value from yacop_cfg}
    }

    foreach obj {src dst db} {
       method $obj {args} [string map [list OBJ $obj] {
          if {[llength $args] == 0} {
             return $OBJ
          }
          uplevel 1 [list $OBJ] $args
       }]
    }

    method extend {region} {
        array set reg $region
        set smin $cfg(sdeg)
        set smax $reg(smax)
        foreach sdeg [$src db eval {
            select distinct sdeg from generators
            where sdeg > $smin and sdeg <= $smax order by sdeg
        }] {
	    Section "Lifting homological degree $sdeg" {
		# try to make us interruptible
		set ::steenrod::_progvarname ::yacop::progVar
		yacop::interruptible {
                    my db transaction {
                        set cond ""
                        if {[info exists reg(nmax)]} {
                            if {$cfg(viewtype) eq "even"} {
                                lappend cond  "(ideg/2-sdeg) <= $reg(nmax)"
                            } else {
                                lappend cond  "(ideg-sdeg) <= $reg(nmax)"
                            }
                        }
                        if {[info exists reg(imax)]} {
                            lappend cond "ideg<=$reg(imax)"
                        }
                        my extend-line $sdeg $cond
                    }
                }
            }
        }
    }
    
    method extend-line {sdeg cond} {

        foreach key {sdeg ideg edeg} {
            set off$key $cfg($key)
        }

        set srcgens [$src db eval {
            select list(rowid,ideg,edeg)
            from generators where sdeg=$sdeg 
            order by ideg,edeg
        }]
        set dstgens_curr [$dst db eval {
            select list(rowid,ideg,edeg)
            from generators where sdeg=$sdeg-$offsdeg 
            order by ideg,edeg
        }]
        set dstgens_prev [$dst db eval {
            select list(rowid,ideg,edeg)
            from generators where sdeg=$sdeg-$offsdeg-1 
            order by ideg,edeg
        }]      

        set dstisnegative [expr {$cfg(algmap) eq "psi"}]

        steenrod::enumerator SRC -algebra {0 0 0 0} -prime $srccfg(prime)
        foreach d {DSTcurr DSTprev DSTfull} {
            steenrod::enumerator $d \
                -algebra [steenrod::algebra tomono $dstcfg(algebra) 8] -prime $dstcfg(prime)
            if {$dstisnegative} { $d configure -type negative -algebra $cfg(negalg) } 
        }
        
        SRC configure -genlist $srcgens
        DSTcurr configure -genlist $dstgens_curr
        DSTprev configure -genlist $dstgens_prev
        DSTfull configure -genlist $dstgens_prev

        steenrod::monomap phi.prev

        $src db eval {
            select rowid from generators where sdeg=$sdeg-1
        } {
            my db eval {
                select frag_decode(format,data,targen) as data
                from fragments where srcgen =$rowid
            } {
                phi.prev append [list 1 0 0 $rowid] $data 
            }
        }

        steenrod::monomap d.dst
        
        $dst db eval [subst {
            select rowid from generators where [join [linsert $cond 0 {sdeg=$sdeg-$offsdeg}] { and }]
        }] {
            $dst db eval {
                select frag_decode(format,data,targen) as data
                from fragments where srcgen =$rowid
            } {
                d.dst append [list 1 0 0 $rowid] $data
            }
        }

        set prime $srccfg(prime)

        set frobenius [expr {$cfg(algmap) eq "frobenius"}] 

        foreach m {phi.prev d.dst} {
            #puts $m:[$m list]
        }

        set dstcfg(algmono) [steenrod::algebra tomono $dstcfg(algebra) 8]

        set cond [linsert $cond 0 {sdeg=$sdeg}]
        $src db eval [subst {
            select group_concat(rowid,' ') as ids,ideg,edeg from generators
            where [join $cond { and }] group by ideg,edeg order by ideg,edeg
        }] {
            
            set alreadydone 0
            foreach id $ids {
               if {[my db eval {select count(*) from generators where rowid=$id}]} {
                  set alreadydone 1
                  break
               }
            }
            if {$alreadydone} continue

            set dideg [expr {$ideg-$offideg}]
            set dedeg [expr {$edeg-$offedeg}]
            set dsdeg [expr {$sdeg-$offsdeg}]
            if {$frobenius} {
                if {$edeg || 0 != ($dideg % $prime)} {
                    # nothing to do
                    foreach id $ids {
                        my db eval {
                            insert into generators(rowid) values($id)
                        } 
                    }
                    continue
                }
                set dideg [expr {$dideg/$prime}]
            }
            #puts sdeg:$sdeg,ideg:$ideg,edeg:$edeg,ids=$ids,dsdeg=$dsdeg,dideg=$dideg,dedeg=$dedeg
            SRC configure -ideg $ideg -edeg $edeg
            DSTcurr configure -ideg $dideg -edeg $dedeg
            DSTprev configure -ideg $dideg -edeg $dedeg
            DSTfull configure  -ideg $dideg -edeg $dedeg
            #puts sbas:[SRC basis]
            #puts dful:[DSTfull basis]

            foreach enum {DSTfull DSTcurr DSTprev} {
                #puts "$enum [$enum configure]"
            }

            set diffs {}
            foreach gen $ids {
                set dgen [steenrod::poly create]
                $src db eval {
                    select frag_decode(format,data,targen) as data
                    from fragments where srcgen=$gen 
                } {
                    if {$frobenius} {
                        # apply (dual of) Frobenius map
                        set ndata {}
                        foreach m $data {
                            foreach {cf e r g} $m break
                            if {$e} continue
                            set r2 {}
                            set ok 1
                            foreach x $r {
                                if {0 != ($x % $prime)} {
                                    set ok 0
                                    break
                                }
                                lappend r2 [expr {$x/$prime}]
                            }
                            if {$ok} {
                                lappend ndata [list $cf 0 $r2 $g]
                            }
                        }
                        set data $ndata
                    }
                    steenrod::poly varappend dgen $data
                }
                #puts gen:$gen->$dgen
                lappend diffs $dgen
            }
            #puts [list diffs = $diffs]
if {0&&$dstisnegative} {
parray cfg
puts "diffs=$diffs,[DSTfull configure]"
puts "[DSTfull basis]"
}
            set tolift [steenrod::ComputeImage phi.prev DSTfull $diffs]
            #puts tolift=[join $tolift \n]

            set mode auto
            if {$dstisnegative} {set mode none} ;# FIXME

            set prof [yacop::gfr_tools::findBestProfile [namespace which DSTprev] \
                          $dstcfg(prime) $dstcfg(algmono) [expr {$dsdeg-0}] $dideg $dedeg $mode]
            #puts prof=$prof
            
            DSTcurr configure -profile $prof
            DSTprev configure -profile $prof

            unset -nocomplain phi
           
            DSTcurr sigreset
            DSTprev sigreset
            while on {
                #puts currsig=[DSTcurr cget -signature],prevsig=[DSTprev cget -signature]
                DSTcurr configure -signature [DSTprev cget -signature]

                #puts DSTcurr.basis=[DSTcurr basis]
                #puts DSTprev.basis=[DSTprev basis]

                # extract terms of this signature:
                set seqmap [DSTfull seqno DSTprev]
                set submat [steenrod::matrix extract cols $tolift $seqmap]
                
                #puts tolift([DSTprev cget -signature])=$submat
              
if {0&&$dstisnegative} {
foreach d {DSTcurr DSTprev} {
puts $d[$d configure]
puts [$d basis]
}
}

                # compute relevant part of matrix DSTcurr -> DSTprev
                set mdsn [steenrod::ComputeMatrix DSTcurr d.dst DSTprev]
                #puts mdsn=$mdsn

                # compute lift
                set lft [steenrod::matrix liftvar $prime mdsn submat]
                #puts lft=$lft,submat=$submat

                if {![steenrod::matrix iszero $submat]} {
                    error "internal error: chosen subalgebra probably too big"
                }

                set cnt 0
                set corrections {}
                foreach id $ids {
                    # TODO: use something better than "lindex" here!
                    set preim [lindex [steenrod::matrix extract row $lft $cnt] 0]
                    lappend corrections [set aux [DSTcurr decode $preim -1]]
                    #puts phi($id)+=$aux
                    steenrod::poly varappend phi($id) $aux
                    incr cnt
                }
 
                # update tolift
                steenrod::matrix addto tolift \
                    [steenrod::ComputeImage d.dst DSTfull $corrections] 1 $prime

                if {![DSTcurr signext] || ![DSTprev signext]} break
            }
               
            if {![steenrod::matrix iszero $tolift]} {
                error "internal error: lift not correct"
            }

            foreach id $ids {
                my db eval {
                    insert into generators(rowid) values($id)
                }
                unset -nocomplain pieces
                steenrod::poly foreach $phi($id) mono {
                    lappend pieces([lindex $mono end]) $mono
                }
                foreach {targen data} [array get pieces] {
                    set tideg [$dst db onecolumn {
                        select ideg from generators where rowid=$targen
                    }]
                    set opdeg  [expr {$dideg-$tideg}]
                    my db eval {
                        insert into fragments(srcgen,targen,opideg,format,data)
                        values($id,$targen,$opdeg,'tcl',$data)
                    }
                    #if {$opdeg == 0} {puts $id->$targen}
                }
            }
        }
        
    }

    method pullback {cycle} {
        set p $dstcfg(prime)
        array set res {}
        foreach {cf id} $cycle {
            my db eval {
                select srcgen,frag_decode(format,data,targen) as data
                from fragments where opideg=0 and targen=$id
            } {
                foreach m $data {
                    foreach {c e r tg} $m break
                    incr res($srcgen) [expr {$cf*$c}]
                }
            }
        }
        array get res
    }
    
}

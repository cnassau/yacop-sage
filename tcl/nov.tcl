package req yacop
package req yacop::sage ;# this shouldn't be necessary !

set yacop::sectionizer::quiet 1

set p 3

yacop::gfr create resolution :memory:
resolution algebra $p {-1 full}
resolution extend-to {sdeg 10 tdeg 60}

set tcl_interactive 1

source ~/misc/secmult/ebp.tcl

oo::class create novikov {

    variable {*}{
	prime db resolution
    }

    constructor {gfr} {
	set resolution $gfr
	set db [$gfr db]
	set prime [dict get [$gfr config] prime]  

	namespace path [list {*}[namespace path] ::yacop::sectionizer]

	my make-tables
    }

    export db extend-to

    method db {args} {
        if {[llength $args] == 0} {
            return $db
        }
        uplevel 1 [list $db] $args
    }

    method make-tables {} {
	set sql {
	    create table if not exists 
	    %TABLE%(/* the summands of the novikov differential */
		    rowid integer primary key,
		    srcgen integer, /* rowid of source generator */
		    targen integer, /* rowid of target generator */
		    mudeg integer,  /* exterior degree of the mu-part */
		    format text,    /* how data is encoded */
		    data text       /* the data */);   
	}
	foreach tab {nov_fragments nov_errors} {
	    my db eval [string map [list %TABLE% $tab] $sql]
	}
    }
    
    method extend-to {sdeg n} { 
	for {set s 0} {$s < $sdeg} {incr s} {	    
	    Section "Extending EBP resolution to s=$s and dim $n" {
		# try to make us interruptible
		set ::steenrod::_progvarname ::yacop::progVar
		yacop::interruptible {
		    my db eval {
			select rowid from generators 
			where sdeg=$s and ideg<= $n+sdeg
			order by id
		    } {
			my Extend-generator $rowid
		    }
		}
	    }
	}
    }

    method Make'd1 {rowid} {	
	my db eval {
	    select 
	    frag_decode(format,data,targen) as data,
	    targen 
	    from fragments where srcgen = $rowid
	    order by targen
	} {
	    #puts "$rowid -> $data"
	    set nfrag {}
	    steenrod::poly foreach $data m {
		#foreach {cf mu v P Q} $m break
		foreach {cf Q P tg} $m break
		lappend nfrag [list $cf 0 {} $P $Q]
	    } 
	    #puts [fmtop $nfrag]
	    my Add-Fragment $rowid $targen $nfrag 
	}
    }


    method Foreach'diff {resvar rowid script} {
        upvar 1 $resvar res
        my db eval {
            select n.data as data, 
                   n.targen as targen,
                   tg.sdeg as tsdeg,
                   tg.ideg as tideg,
                   tg.edeg as tedeg
            from nov_fragments n 
            join generators as tg on tg.rowid = n.targen
            where n.srcgen = $rowid
        } res {
            uplevel 1 $script
        }
    }

    method Make'dsquare {rowid} {
        array set tot {}
        my Foreach'diff df $rowid {
           set sgn [expr {(1 & ($df(tedeg) + $df(tsdeg))) ? -1 : 1}]
           set part [EBP partial $prime $df(data)]
           set x [EBP cancel $prime [EBP scale $part $sgn]]
           lappend tot($df(targen)) {*}$x
           my Foreach'diff ddf $df(targen) {
              set prod [EBP multiply $prime $ddf(data) $df(data)]
#verbose-multiply $prime $ddf(data) $df(data)            
  lappend tot($ddf(targen)) {*}$prod
           }
        }
        foreach x [array names tot] {
           set tot($x) [set r [EBP cancel $prime $tot($x)]]
           if {0 == [llength $r]} {
              unset tot($x)
           }
        }
        parray tot
        array get tot
    }

    method Extend-generator {rowid} {
	my db eval {
	    select sdeg, ideg, edeg, id, basid, ideg-sdeg as topdim
	    from generators where rowid=$rowid
	} break
	Section "\[$id\] / dim $topdim, rowid $rowid" {
	    my Make'd1 $rowid

	    if 1 {
		# sanity check
		my db eval {
		    select 
		    group_concat(data,' ') as sumdata, 
		    targen 
		    from nov_errors 
		    join generators tg on tg.rowid = nov_errors.targen
		    where srcgen=$rowid and tg.sdeg = $sdeg-2
		    group by targen
		} {
		    EBP Areduce $prime $sumdata -> ared
		    steenrod::poly varcancel ared $prime
		    if {[steenrod::poly compare $ared {}]} {
			puts ared=$ared
			puts "$rowid -> $targen * ([fmtop $sumdata]) != 0"
			my Report'problem $rowid $targen
			exit 1
		    }
		}
	    }

	    for {set k 2} {$k<=$sdeg} {incr k} {
		Section "d$k" {
		    my Make'dk $rowid $k
		}
	    }

            set x [my Make'dsquare $rowid]
            puts tot:$x
	    if {$x ne ""} {
		my Report'problem $rowid [lindex $x 0]
		puts stderr "d^2($rowid) = $x \n = \[[lindex $x 0]\] * ([fmtop [lindex $x 1]]) + ...\n != 0"
		exit 1
	    }
        }
    }

    method Report'target {rowid} {
	my db eval {
	    select data,targen from nov_fragments
	    where srcgen=$rowid
	} {
	    puts [format {  [%d] -> [%d] * (%s)} \
		      $rowid $targen [fmtop $data]]
	}
    }

    method Report'problem {rowid targen} {
	puts "Matrix coefficient problem $rowid -> $targen"
	my db eval {
	    select sdeg, ideg, edeg, id, basid, ideg-sdeg as topdim
	    from generators where rowid=$rowid
	} break
	puts "nov_fragments:"
	my Report'target $rowid
	my db eval {
	    select distinct targen as targ from nov_fragments
	    where srcgen=$rowid order by targen
	} {
	    my Report'target $targ
	}
	puts "multiplications:"
	my db eval {
	    select n1.data as d1, n2.data as d2 from nov_fragments as n1
	    join nov_fragments as n2 on n1.targen = n2.srcgen
	    where n1.srcgen=$rowid and n2.targen=$targen 
	} {
	    verbose-multiply $prime $d2 $d1
	}
	puts "nov_errors:"
	nov db eval {
	    select targen, data from nov_errors
	    where srcgen=$rowid order by targen
	} {
	    puts [format {         [%d] %s} $targen [fmtop $data]]
	}
    }

    method Find'lifting'degrees {sdeg poly -> svar ivar evar} {
	upvar 1 $svar s $ivar i $evar e
	set mono [lindex $poly 0]
	set medeg [steenrod::mono edegree $mono]
	set mideg [steenrod::mono degree $prime $mono]
	set id [lindex $mono end]
	my db eval {
	    select edeg,ideg from generators
	    where sdeg = $sdeg and id = $id
	} break
	incr medeg $edeg
	incr mideg $ideg
	set s $sdeg
	set e $medeg
	set i $mideg
    }

    method Adjust'partialsigns {arrvar} {
	upvar 1 $arrvar newdiff
	
	# we're using d(ga) \contains g * (-1)^g \partial a
	# we therefore need to compute (-1)^g for each g in d$new
	
	foreach targen [array names newdiff] {
	    set targparity [my db onecolumn {
		select sdeg-edeg from generators where rowid=$targen
	    }]
	    if {$targparity & 1} {
		set negsign -1
	    } else {
		set negsign 1
	    }
	    set smd $newdiff($targen)
	    set neg [EBP cancel $prime [EBP scale $smd $negsign]]
	    set newdiff($targen) $neg
	}
    }

    method Add'arraydiff {rowid arrvar {scale 1}} {
	upvar 1 $arrvar newdiff
	parray newdiff
	foreach {targen smd} [array get newdiff] {
	    puts ">> $targen += [fmtop $smd]<<"
	    if {$scale != 1} {
		set smd [EBP cancel $prime [EBP scale $smd $scale]]
	    }
	    my Add-Fragment $rowid $targen $smd
	}
    }
  
    method Verify'multiplication {m1 m2} {
        foreach {cf1 Q1 P1 id1} $m1 break
        foreach {cf2 Q2 P2 id2} $m2 break
        set pl1 [list $m1]
        set pl2 [list $m2]
        set aux [steenrod::poly steenmult $pl2 $pl1 $prime]

        set epl1 [list [list $cf1 0 {} $P1 $Q1]] 
        set epl2 [list [list $cf2 0 {} $P2 $Q2]] 

        set bux [EBP multiply $prime $epl1 $epl2]

        set cux {}
        foreach smd $bux {
            foreach {cf mu v P Q id} $smd break
            if {$v eq "" && (0 != ($cf % $prime))} {
               if {$mu != 0} {lappend error "mu not zero: $mu"}
               lappend cux [list $cf $Q $P $id1]
            }
        }

        steenrod::poly varcancel aux $prime
        steenrod::poly varcancel cux $prime

        if {[steenrod::poly compare $aux $cux]} {
            set error "results differ"
        } 

        if {[info exists error]} {
            puts "sanity check failed: ([polyfmt {cf Q P g} $pl2]) * ([polyfmt {cf Q P g} $pl1])"
            puts "sanity check failed: aux = [polyfmt {cf Q P g} $aux]"
            puts "sanity check failed: cux = [polyfmt {cf Q P g} $cux]"
            puts "sanity check failed: $error"
            verbose-multiply $prime $epl1 $epl2
            exit 1
        }
   
        puts "sanity check passed: ($pl2) * ($pl1) = ($aux)"
    }
 
    method Check'lift'sanity {vct} {
 puts "sanity check $vct"
       # make sure differential in C* agrees with EBP diff mod I

       steenrod::poly foreach $vct m {
          foreach {cf Q P id} $m break
          my db eval {
             select data, targen from fragments where srcgen=$id
          } { 
             steenrod::poly foreach $data smd {
                 my Verify'multiplication $smd $m ;#$smd
             }      
          }
       }


    }
 
    method Make'dk {rowid k} {
	my db eval {
	    select sdeg, ideg, edeg, id, basid, ideg-sdeg as topdim
	    from generators where rowid=$rowid
	} break

	set lastv 1000
	set lastmu 0xffff

	while on {
	    # collect Xk([rowid]) from nov_errors

	    set xkmodI {}
	    unset -nocomplain Xk
	    unset -nocomplain newdiff
	    array set Xk {}

	    set obstacles {}
	    set obstv -1
	    set obstmu -1

	    set tgsdeg [expr {$sdeg-$k}]

	    my db eval {
		select 
		group_concat(n.data,' ') as sumdata, 
		n.targen, tg.id as id, tg.edeg as tgpar 
		from nov_errors as n
		join generators as tg on tg.rowid = targen 
		where srcgen=$rowid and tg.sdeg = $tgsdeg
		group by targen
		order by targen
	    } {
		EBP Areduce $prime $sumdata -> ared rest
		#puts "\[$targen\] * ([fmtop $sumdata]) ->\n  A-part = $ared\n  Rest = [fmtop $rest]"
		steenrod::poly foreach $ared m {
		    lset m end $id
		    lappend xkmodI $m
		}
		EBP try-departial $prime $rest -> depart maxv maxmu newobst
		if {[llength $newobst]} {
		    if {($maxv > $obstv)
			|| ($maxv == $obstv && $maxmu > $obstmu)} {
			set obstacles {}
			set obstv $maxv
			set obstmu $maxmu
		    } 
		    if {$maxv == $obstv && $maxmu == $obstmu} {
			steenrod::poly foreach $newobst m {
			    lset m end $id
                          if {1 & bitcount($obstmu)} {
			    # sign tweaking: from [g] * mu(...) * x => mu(...) [g] * x
                            if {1 & $tgpar} {
                                puts "tweaking obstacles I"
                                lset m 0 [expr {-[lindex $m 0]}]
                            }
                          }
                            lappend obstacles $m
			}
		    }
		} else {
		    if {[llength $depart]} {
			set Xk($targen) $depart
		    }
		}
	    }
	    
	    if {[llength $obstacles]} {
		set lastv $obstv
		set lastmu $obstmu
		set lsdeg [expr {$sdeg-$k}]
		set powers [steenrod::prime $prime powers]

		my Find'lifting'degrees $lsdeg $obstacles -> s i e

                my NoRepeat "obstacles >$obstacles< in ($s,$i,$e)"

		puts "need d1-lift: maxv=$obstv, maxmu=$obstmu for"
		puts "tolift = mu([bitprint $obstmu]) * v$obstv * ([polyfmt {cf Q P g} $obstacles])"
		puts "in degree (s,i,e) = ($s,$i,$e)"
		my Report'problem $rowid $targen


                if {0 && bitcount($obstmu) & 1} {
                  # sign tweaking I: move from  g_k mu($obstmu) to mu($obstmu) g_k 
                  set o2 {}
                  steenrod::poly foreach $obstacles mo {
                     foreach {cf Q P id} $mo break
                     set gpar [my db onecolumn {
                        select sdeg-edeg from generators where sdeg=$tgsdeg and id=$id
                     }]              
                    if {$gpar & 1} {
                        puts "tweak I"
                        set cf [expr {(-$cf)%$prime}]
                    }
                     lappend o2 [list $cf $Q $P $id]
                  }
                set obstacles $o2
                }


		set x [$resolution lift $s $i $e [list $obstacles]]
		set lft [lindex $x 1]
	        set lft2 {}
                
		unset -nocomplain newdiff
		set veff $obstv
		if {$veff == 0} {set veff ""}
		steenrod::poly foreach $lft m {
		    foreach {cf Q P df} $m break
                    set dfpar [my db onecolumn {
                        select edeg from generators
                        where sdeg=$tgsdeg+1 and id=$df
                    }]
                    if {(1 & bitcount($obstmu)) && (1 & $dfpar)} {
                        # sign tweaking II: go back from mu(..) h_k to h_k mu(...)
                        puts "tweak II"
                        set cf [expr {(-$cf)%$prime}]
                    }
		    if {$obstv == 0} {
			set cf [expr {$prime * $cf}]
		    }
		    if {![info exists id2rid($df)]} {
			set id2rid($df) [my db onecolumn {
			    select rowid from generators where 
			    sdeg = $tgsdeg+1 and id = $df
			}]
		    }
		    set tgid $id2rid($df)
                    lappend lft2 [list [lindex $m 0] $Q $P $tgid]
		    lappend newdiff($tgid) [list $cf $obstmu $veff $P $Q]
		}

                my Check'lift'sanity $lft2	
	
                if {0 && bitcount($obstmu) & 1} {

		    # sign logic: we're setting d(g) += h * mu(...) * lift
		    # which gives d(d(g)) = sign * mu(...) * d(h) * lift + ...
		    # where sign is (-1)^{|mu(...)| * |dh|}

		    foreach {x val} [array get newdiff] {
			if {[llength $val]} {
			    
			    if {1 & bitcount([lindex $val 0 end])} {
puts need.reverse,$val
				set newdiff($x) \
				    [EBP cancel $prime [EBP scale $val -1]]
			    }
			}
		    }
		}
                 	
                #my Adjust'partialsigns newdiff
		my Add'arraydiff $rowid newdiff -1

		continue
	    } elseif {[llength [array names Xk]]} {		

		my Adjust'partialsigns Xk
		my Add'arraydiff $rowid Xk -1

		continue
	    } else {
		if {[llength $xkmodI]} {
		    puts "lift needed:"
		    puts xkmodI=$xkmodI

		    
                    set xsdeg $tgsdeg

		    my Find'lifting'degrees $xsdeg $xkmodI -> s i e

                    my NoRepeat "$xkmodI in ($s,$i,$e)"

		    set x [$resolution lift $s $i $e [list $xkmodI]]
		    set lft [lindex $x 1]
		    puts lft=$lft
		    set lft2 {}

		    steenrod::poly foreach $lft m {
			foreach {cf Q P df} $m break
			if {$obstv == 0} {
			    set cf [expr {$prime * $cf}]
			}
			if {![info exists id2rid($df)]} {
			    set id2rid($df) [my db onecolumn {
				select rowid from generators where 
				sdeg = $tgsdeg+1 and id = $df
			    }]
			}
			set tgid $id2rid($df)
                        lappend lft2 [list [lindex $m 0] $Q $P $tgid]
			lappend newdiff($tgid) [list $cf 0 {} $P $Q]
		    }
                    
                    my Check'lift'sanity $lft	
		    
		    my Add'arraydiff $rowid newdiff -1
		    continue
		}
	    }
	    break
	}
    }


    method NoRepeat {value} {
        upvar 1 hist hist
        if {[info exists hist($value)]} {
           puts stderr "endless loop detected: $value"
           exit 1
        }
        set hist($value) .
    }

    method Add-Fragment {rowid targ nfrag} {
	my db eval {
	    select sdeg, ideg, edeg, id, basid, ideg-sdeg as topdim
	    from generators where rowid=$rowid
	} break
	puts [format {d([%d]) += [%d] * (%s)} $rowid $targ [fmtop $nfrag]]
	my db eval {
	    insert into nov_fragments(srcgen,targen,
				      format,data)
	    values($rowid,$targ,'tcl',$nfrag);
	} 
	array set errors {}
	set part [EBP partial $prime $nfrag] 
	set targparity [my db onecolumn {
	    select sdeg-edeg from generators where rowid=$targ
	}]
	if {$targparity & 1} {
	    set part [EBP scale $part -1]
	}
	if {[llength $part]} {
	    lappend errors($targ) $part
	}  
	my db eval {
	    select format,data,targen from nov_fragments
	    where srcgen=$targ
	} {
	    set prod [EBP multiply $prime $data $nfrag]
	    lappend errors($targen) $prod
	    if 0 {
		# sanity check
		EBP Areduce $prime $nfrag -> a1
		EBP Areduce $prime $data  -> a2
		EBP Areduce $prime $prod  -> a3
		set sp [steenrod::poly steenmult $a1 $a2 $prime]
		foreach v {a1 a2 a3 sp} {
		    steenrod::poly varcancel $v $prime
		}
		if {[steenrod::poly compare $a3 $sp]} {
		    puts [format {%d->%d: (%s)*(%s)=%s} $rowid $targen \
			      [fmtop $nfrag] [fmtop $data] [fmtop $prod] ]
		    puts "($a1)*($a2)=($sp), not ($a3)"
		    exit 1
		}
	    }
	}
	foreach {targen val} [array get errors] {
            foreach x $val {
	        puts [format {   d^2([%d]) += [%d] * (%s)} $rowid $targen [fmtop $x]]
            }
	    set oldval [my db onecolumn {
		select group_concat(data,' ') from nov_errors
		where srcgen=$rowid and targen=$targen
	    }]
	    my db eval {
		delete from nov_errors where srcgen=$rowid and targen=$targen
	    }
	    #puts oldval=$oldval,val=$val
	    set diff [EBP sum $prime $oldval {*}$val]
	    #puts diff=$diff
	    my db eval {
		insert into nov_errors(srcgen,targen,
				       format,data)
		values($rowid,$targen,'tcl',$diff);
	    }
	}
    }

}

novikov create nov resolution

#puts [nov db eval {select count(*) from generators}] 
set yacop::sectionizer::quiet 0

nov extend-to 10 20
nov db eval {
    select srcgen, targen, data from nov_errors
    order by srcgen, targen
} {
    puts [format {[%d] -> [%d] %s} $srcgen $targen [fmtop $data]]
}

if 0 {
    nov db eval {
	select distinct srcgen,g.sdeg as sdeg, g.ideg-g.sdeg as tdeg
	from nov_fragments join generators g
	on g.rowid = srcgen order by g.ideg-g.sdeg, g.sdeg
    } {
	puts "== \[$srcgen\] ($sdeg,$tdeg)  -> =============="
	nov db eval {
	    select data, targen from nov_fragments
	    where srcgen=$srcgen order by $targen
	} {
	    puts [format {   [%d] %s} $targen [fmtop $data]]
	}
	puts "     =>"
	nov db eval {
	    select targen, data from nov_errors
	    where srcgen=$srcgen order by targen
	} {
	    puts [format {         [%d] %s} $targen [fmtop $data]]
	}
    }
}

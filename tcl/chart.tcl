#
# Graphical user interface
#
# Copyright (C) 2009-2018 Christian Nassau <nassau@nullhomotopie.de>
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License version 2 as
# published by the Free Software Foundation.
#

oo::class create yacoptoplevel {

    variable top tcnt

    constructor {} {
        set top .tp[incr tcnt]

        toplevel $top -relief flat
        wm withdraw $top
        if {$::tk_version >= 8.4
            && [string equal [tk windowingsystem] "aqua"]} {
            ::tk::unsupported::MacWindowStyle style $top help none
        } else {
            wm overrideredirect $top 1
        }

        catch { wm attributes $top -topmost 1 }
    }

    destructor {
        catch {destroy $top}
    }

    method center {x y} {
        update idletasks

        if {![winfo exists $top]} {return}

        set  width     [winfo reqwidth  $top]
        set  height    [winfo reqheight $top]
        incr y [expr {-$height/2}]
        incr x [expr {-$width/2}]

        wm geometry  $top "+$x+$y"
        update idletasks

        if {![winfo exists $top]} { return }
        wm deiconify $top
        raise $top
    }

    method corner {x y} {
        update idletasks

        if {![winfo exists $top]} {return}

        wm geometry  $top "+$x+$y"
        update idletasks

        if {![winfo exists $top]} { return }
        wm deiconify $top
        raise $top
    }
}

oo::class create labelwin {
    superclass yacoptoplevel
    variable top parent zoom
    constructor {x y text args} {
        next
        pack [ttk::label $top.lab -text $text {*}$args] -side top -expand 1 -fill both
        my corner $x $y
    }
}

oo::class create magnifier {
    superclass yacoptoplevel
    variable top parent zoom
    constructor {x y owner zoomfactor} {
        next
        set parent $owner
        set zoom $zoomfactor
        pack [ttk::frame $top.tb] -side top
        pack [ttk::label $top.tb.lab -text ZOOM!] -side left
        pack [canvas $top.c -width 600 -height 400 -background [set [$parent cfgvar lensebg]]] \
            -side top -expand 1 -fill both
        focus $top.c
        bind $top <Motion> [list [self] follow-mouse]
        bind $top.c <ButtonRelease> [list [self] destroy]
        bind $top.c <Key-Escape> [list [self] destroy]
        bind $top <Destroy> [list $owner mode idle]
        my follow-mouse
    }

    method follow-mouse {} {
        my variable top
        my center {*}[winfo pointerxy $top]
        my clone
    }

    method clone {} {
        set mx1 [winfo rootx $top.c]
        set my1 [winfo rooty $top.c]
        set w [winfo width $top.c]
        set h [winfo height $top.c]
        set mx2 [expr {$mx1+$w}]
        set my2 [expr {$my1+$h}]
        set mcx [expr {$mx1+$w/2.0}]
        set mcy [expr {$my1+$h/2.0}]

        set pcvs [$parent cvs]

        set prx [winfo rootx $pcvs]
        set pry [winfo rooty $pcvs]

        set cx1 [$pcvs canvasx [expr {$mx1-$prx}]]
        set cx2 [$pcvs canvasx [expr {$mx2-$prx}]]
        set cy1 [$pcvs canvasy [expr {$my1-$pry}]]
        set cy2 [$pcvs canvasy [expr {$my2-$pry}]]

        set ccx [expr {($cx1+$cx2)/2.0}]
        set ccy [expr {($cy1+$cy2)/2.0}]

        set cwh [expr {($cx2-$cx1)/(2.0*$zoom)}]
        set chh [expr {($cy2-$cy1)/(2.0*$zoom)}]

        lappend creg [expr {$ccx-$cwh}] [expr {$ccy-$chh}]
        lappend creg [expr {$ccx+$cwh}] [expr {$ccy+$chh}]

        set mx [expr {[$top.c cget -width]/2.0}]
        set my [expr {[$top.c cget -height]/2.0}]

        $top.c delete copy
        #foreach v [info vars] { set vars($v) [set $v]};parray vars
        #puts creg=$creg
        foreach id [$pcvs find overlapping {*}$creg] {
            set tp [$pcvs type $id]
            set nco {}
            foreach {ix iy} [$pcvs coords $id] {
                lappend nco [expr {$zoom*($ix-$ccx)+$mx}] [expr {$zoom*($iy-$ccy)+$my}]
            }
            set opts {}
            foreach {optdesc} [$pcvs itemconfigure $id] {
                lappend opts [lindex $optdesc 0] [lindex $optdesc end]
            }
            $top.c create $tp {*}$nco {*}$opts -tag copy
        }
    }
}


set bitmaps(dot1) {
    name {circle}
    data {
        #define a_width 5
        #define a_height 5
        #define a_x_hot 3
        #define a_y_hot 3
        static unsigned char a_bits[] = {
            0x0e, 0x1f, 0x1f, 0x1f, 0x0e
        };
    }
}
set bitmaps(dot2) {
    name {big circle}
    data {
        #define a_width 11
        #define a_height 11
        #define a_x_hot 6
        #define a_y_hot 6
        static unsigned char a_bits[] = {
            0xf8, 0x00, 0xfc, 0x01, 0xfe, 0x03, 0xff, 0x07, 0xff, 0x07, 0xff, 0x07,
            0xff, 0x07, 0xff, 0x07, 0xfe, 0x03, 0xfc, 0x01, 0xf8, 0x00
        };
    }
}
set bitmaps(dot3) {
    name {square}
    data {
        #define a_width 7
        #define a_height 7
        #define a_x_hot 4
        #define a_y_hot 4
        static unsigned char a_bits[] = {
            0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f
        };
    }
}
set bitmaps(dot4) {
    name {big square}
    data {
        #define a_width 11
        #define a_height 11
        #define a_x_hot 6
        #define a_y_hot 6
        static unsigned char a_bits[] = {
            0xff, 0x07, 0xff, 0x07, 0xff, 0x07, 0xff, 0x07, 0xff, 0x07, 0xff, 0x07,
            0xff, 0x07, 0xff, 0x07, 0xff, 0x07, 0xff, 0x07, 0xff, 0x07
        };
    }
}

oo::class create chartcvs {

    variable widgets db cfg images colcache opwatch

    constructor {path dbcmd} {

        set db $dbcmd

        array set cfg {
            viewtype {}
            prime    {}
            algebra  {}
            filtcol-0 #000000
            filtcol-1 #808080
            filtstyle novikov
            activefg  #d02020
            canvasbg  white
            lensebg   yellow
            infowinbg #ffff7f
            infowinfg black
            placementmode bycrowdiness
            axisfont TkDefaultFont
            textfont TkDefaultFont
            zoom     4
            mode idle
            dpm {}
            y2x 1.0
            numgens -
        }

        set cfg(dotbitmap) ::bitmaps([lindex [array names ::bitmaps] 0])

        my MakeCanvas $path
        my MakeTables

        trace add variable cfg(mode) write "[list [self] mode] ;#"
        trace add variable cfg(viewtype) write "[list [self] viewtype] ;#"
        trace add variable cfg(filtcol-0) write "[list [self] new-filtcols] ;#"
        trace add variable cfg(filtcol-1) write "[list [self] new-filtcols] ;#"
        trace add variable cfg(filtstyle) write "[list [self] new-filtstyle] ;#"

        # trigger some traces
        array set cfg [array get cfg viewtype]
        my new-filtcols false

        trace add variable cfg(viewtype) write "after idle [list [self] reload] ;#"
        trace add variable cfg(placementmode) write "after idle [list [self] reload] ;#"
        trace add variable cfg(canvasbg) write "[list [self] new-bg] ;#"
        trace add variable cfg(activefg) write "[list [self] new-bg] ;#"
        trace add variable cfg(axisfont) write "[list [self] make-axes] ;#"
        trace add variable cfg(dotbitmap) write "[list [self] new-dotbitmap] ;#"

        trace add variable cfg write "[list [self] configchange]"
    }
    method configchange {name1 name2 op} {
        if {[regexp {^(line.*)-dash} $name2 -> tagname]} {
            my cvs itemconfigure $tagname -state [lindex $cfg($name2) 0] -dash [lindex $cfg($name2) 1]
        }
        if {[regexp {^(line.*)-width} $name2 -> tagname]} {
            my cvs itemconfigure $tagname -width $cfg($name2) -activewidth [expr {1+$cfg($name2)}]
        }
    }
    method set-dpm {newdpm newy2x} {
        set cfg(dpm) $newdpm
        set cfg(y2x) $newy2x
        my new-dpm
    }
    method new-bg {} {
        foreach c {cvs xax yax cul} {
            my $c configure -bg $cfg(canvasbg)
        }
        my cvs itemconfigure line -activefill $cfg(activefg)
        [my Dot active] configure -foreground [my Filtcol active yes]
    }

    method cfgvar {varname} {
        return [namespace current]::cfg($varname)
    }
    method getconfig {} {
        array get cfg
    }
    method db {args} {
        if {[lindex $args 0] eq ""} {return $db}
        uplevel 1 $db $args
    }

    method unknown {cmd args} {
        if {[info exists widgets($cmd)]} {
            lappend map CMD $cmd
            oo::objdefine [self] method $cmd {args} [string map $map {
                my variable widgets
                if {[llength $args]} {
                    uplevel 1 $widgets(CMD) $args
                } else {
                    return $widgets(CMD)
                }
            }]
            my $cmd {*}$args
        } else {
            next $cmd {*}$args
        }
    }
    unexport unknown

    method MakeCanvas {path} {

        set widgets(frame) [set f [ttk::frame $path]]

        set cvsopts {
            -background white -borderwidth 0 -highlightthickness 0
            -width 2 -height 2
        }

        set widgets(cvs) [canvas $f.cvs {*}$cvsopts]
        set widgets(xax) [canvas $f.xax {*}$cvsopts]
        set widgets(yax) [canvas $f.yax {*}$cvsopts]
        set widgets(cul) [canvas $f.cul {*}$cvsopts]

        set widgets(scv) [ttk::scrollbar $f.sch -orient vertical \
                              -command [list [self] yview]]
        set widgets(sch) [ttk::scrollbar $f.scv -orient horizontal \
                              -command [list [self] xview]]
        my cvs configure -yscrollcommand [list [self] set-vert] \
            -xscrollcommand [list [self] set-horiz]

        foreach {var row col opts} {
            yax 1 0 {-sticky news}
            xax 0 1 {-sticky news}
            cvs 1 1 {-sticky news}
            scv 0 2 {-rowspan 2 -sticky news}
            sch 2 0 {-columnspan 2 -sticky news}
            cul 0 0 {-sticky news}
        } {
            grid configure $widgets($var) -row $row -column $col {*}$opts
        }

        foreach subcmd {rowconfigure columnconfigure} {
            foreach idx {0 2} {
                grid $subcmd $f $idx -weight 0
            }
            grid $subcmd $f 1 -weight 1
        }

        foreach {evnt desc} {
            <MouseWheel>      {wheel %D}
            <Button-4>        {wheel -120}
            <Button-5>        {wheel 120}
            <ButtonRelease-1> {evtbtn r1 %x %y %X %Y}
            <ButtonRelease-2> {evtbtn r2 %x %y %X %Y}
            <ButtonRelease-3> {evtbtn r3 %x %y %X %Y}
            <Button-1>        {evtbtn b1 %x %y %X %Y}
            <Button-2>        {evtbtn b2 %x %y %X %Y}
            <Button-3>        {evtbtn b3 %x %y %X %Y}
            <Motion>          {evtbtn motion %x %y %X %Y}
            <Key-Escape>      {evtbtn end %x %y %X %Y}
        } {
            bind $widgets(cvs) $evnt [list [self] {*}$desc]
        }
    }

    method xview args {
        my cvs xview {*}$args
        my xax xview {*}$args
    }
    method yview args {
        my cvs yview {*}$args
        my yax yview {*}$args
    }
    method set-horiz args {
        my sch set {*}$args
    }
    method set-vert args {
        my scv set {*}$args
    }

    method zoom {factorx {factory {}}} {

        # adjust factors to give a nice dpm
        set newdpm [expr {round($cfg(dpm)/$factorx)}]
        set facxnew [expr {$cfg(dpm)/(1.0*$newdpm)}]
        if {$factory ne ""} {
            #set factory [expr {$factory*$facxnew/(1.0*$factorx)}]
        }
        set factorx $facxnew

        if {$factory eq ""} {
            set factory $factorx
            set newy2x $cfg(y2x)
        } elseif {$factorx == $factory} {
            set newy2x $cfg(y2x)
        } else {
            # adjust factory to give a nicer y2x
            set newy2x [expr {round(10*$cfg(y2x)*$factory/(1.0*$factorx))/10.0}]
            set newy2x [format %.1f $newy2x]
            set factory [expr {$factorx*$newy2x/$cfg(y2x)}]
        }

        set factorx [expr {1.0*$factorx}]
        set factory [expr {1.0*$factory}]


        # find center of canvas
        set cx1 [my cvs canvasx 0]
        set cy1 [my cvs canvasy 0]
        set cx2 [my cvs canvasx [winfo width [my cvs]]]
        set cy2 [my cvs canvasy [winfo height [my cvs]]]
        set cmx [expr {($cx1+$cx2)/2.0}]
        set cmy [expr {($cy1+$cy2)/2.0}]

        foreach {xvl xvr} [my cvs xview] break
        foreach {yvl yvr} [my cvs yview] break

        my cvs create rect {*}[my cvs cget -scrollregion] -tag scrollregion
        my cvs create text 0 0 -tag origin
        my cvs scale all $cmx $cmy $factorx $factory
        foreach {ox oy} [my cvs coords origin] break
        my cvs move all [expr {-$ox}] [expr {-$oy}]
        my cvs delete origin
        my cvs configure -scrollregion [my cvs coords scrollregion]
        my cvs delete scrollregion

        set cfg(dpm) $newdpm
        set cfg(y2x) $newy2x
        my make-axes

        set xvl [expr {$xvl+($xvr-$xvl)*($factorx-1)/(2.0*$factorx)}]
        set yvl [expr {$yvl+($yvr-$yvl)*($factory-1)/(2.0*$factory)}]
        if {$xvl<0} {set xvl 0}
        if {$yvl<0} {set yvl 0}
        my xview moveto $xvl
        my yview moveto $yvl
    }

    method viewtype {{newval {}}} {
        set types [my db eval {select name from chart_viewtypes order by name}]
        if {$newval eq ""} {set newval $cfg(viewtype)}
        if {$newval eq ""} {set newval [lindex $types 0]}
        if {!($newval in $types)} {
            error "unknown viewtype \"$newval\", should be one of [join $types {, }]"
        }
        set cfg(viewtype) $newval
        my db eval {
            drop view if exists chart_generators;
            drop view if exists chart_fragments;
            drop view if exists chart_geninfo;
        }
        my db eval [my db onecolumn {select code from chart_viewtypes where name=$newval}]
    }

    method mode {{newmode {}}} {
        if {$newmode eq ""} {
            set newmode $cfg(mode)
        } else {
            set cfg(mode) $newmode
        }
        set cursors {
            idle ""
            scan fleur
            zoom sizing
            busy watch
            inspect arrow
        }
        if {[dict exists $cursors $newmode]} {
            my cvs configure -cursor [dict get $cursors $newmode]
        } else {
            my cvs configure -cursor ""
        }
    }

    method evtbtn {btn x y X Y args} {
        #puts "evtbtn $btn $x $y $args"

        catch {
            set cx [my cvs canvasx $x]
            set cy [my cvs canvasy $y]
        }

        focus $widgets(cvs)

        if {$cfg(mode) eq "idle"} {
            switch -- $btn {
                b2 {my mode scan}
                b1 {my mode scan}
                b3 {
                    my mode lense
                    magnifier create lense $X $Y [self] $cfg(zoom)
                }
            }
        }

        switch -- $cfg(mode) {
            scan {
                switch -- $btn {
                    b1 {
                        if {[info exists cfg(move-xy)]} return
                        my cvs scan mark $x $y
                        my xax scan mark $x 0
                        my yax scan mark 0 $y
                        set cfg(move-xy) [list $x $y]
                    }
                    r1 {
                        unset -nocomplain cfg(move-xy)
                        my mode idle
                    }
                    motion {
                        if {![info exists cfg(move-xy)]} return
                        my cvs scan dragto $x $y 1
                        my xax scan dragto $x  0 1
                        my yax scan dragto  0 $y 1
                    }
                }
            }
            zoom {
                if {$btn eq "b1"} {
                    if {[info exists cfg(zoom-xy)]} {
                        set btn end
                    } else {
                        set cfg(zoom-xy) [list $cx $cy]
                        my cvs create rectangle $cx $cy $cx $cy \
                            -dash {-..} -width 1 -tags zoom \
                            -outline red -fill lightgrey
                        my cvs lower zoom
                        return
                    }
                }
                if {![info exists cfg(zoom-xy)]} return
                foreach {ox oy} $cfg(zoom-xy) break
                foreach {varname exp} {
                    xmin min($ox,$cx)
                    xmax max($ox,$cx)
                    ymin min($oy,$cy)
                    ymax max($oy,$cy)
                } {
                    set $varname [expr $exp]
                }

                switch -- $btn {
                    motion {
                        my cvs coords zoom $xmin $ymin $xmax $ymax
                        return
                    }
                    end - b3 {
                        if {$btn eq "end"} {
                            #puts "newbounds $xmin $ymin $xmax $ymax"
                            set sreg [list $ymin $ymax $xmax $xmin]
                            #$cvs configure -scrollregion $sreg
                        }
                        my cvs delete zoom
                        unset cfg(zoom-xy)
                        my mode idle
                        return
                    }
                }

            }
            inspect {

                set id [my cvs find withtag current]
                set tags [my cvs gettags $id]

                set desc ""
                if {[catch {
                    if {[lsearch -exact $tags dot] >= 0} {
                        my db eval {
                            select sdeg,ndeg,edeg,basid from chart_generators
                            where rowid in (select genid from dots where cvsid=$id)
                        } {
                            set dim [my db eval {
                                select count(*) as dim from chart_generators
                                where sdeg = $sdeg and ndeg=$ndeg
                            }]

                            set desc "g($sdeg,$ndeg"
                            if {$basid} {
                                append desc ,$basid
                            }
                            append desc ")"
                            if {$edeg} {
                                append desc "\n\nedeg: $edeg"
                            }
                        }
                    } elseif {[lsearch -exact $tags line] >= 0} {


                    }
                } errmsg]} {
                    puts "user-query: $errmsg"
                    return
                }

                catch {rename tinfo {}}
                if {$desc ne ""} {
                    labelwin create tinfo [expr {$X+10}] [expr {$Y+10}] $desc \
                        -relief raised -background $cfg(infowinbg) \
                        -foreground $cfg(infowinfg) -padding 5 -font $cfg(textfont)
                }
            }
        }
    }

    method wheel {delta} {
        my yview scroll [expr {int($delta/120.0)}] units
    }

    method MakeTables {} {
        my db eval {
            create temporary table if not exists
            dots (genid integer primary key,
                  cvsid integer unique,
                  x real,
                  y real,
                  filt integer);
            create temporary table if not exists
            lines (cvsid integer primary key,
                   srcgen integer,
                   targen integer,
                   coeff integer,
                   type text);
        }
	array set cfg {
	    flavour regular
	}
        array set cfg [my db eval {
            select key, value from yacop_cfg
            where key in ('algebra','prime', 'flavour')
        }]

        # create list of P_t^s for this prime and
        # register our pts-search function
        unset -nocomplain opwatch
        set p $cfg(prime)
        set opdegs {}

        lappend opwatch(ptslist) unit
        lappend opwatch(0) {1 0 {} 0} unit
        set opwatch(unit,deg) 0
        set opwatch(unit,op) {1 0 {} 0}
        set opwatch(unit,name) "differential"
        lappend opdegs 0

	set alg $cfg(algebra)
	if {$cfg(flavour) eq "motivic"} {
	    set ealg [steenrod::algebra tomono $alg]
	    set e 0
	    set r {}
	    set aux 1
	    foreach c [lindex $ealg 2] {
		if {$c} { incr e $aux }
		incr aux $aux
		lappend r [expr {$c-1}]
	    }
	    set alg [list $e $r]
	}

        foreach pts [steenrod::algebra ptslist $alg 7] {
            set op [steenrod::algebra pts2op $p $pts]
            set opdeg [steenrod::mono degree $p $op]
            if {$opdeg<0} continue ;# integer overflow
            lappend opwatch(ptslist) $pts
            lappend opwatch($opdeg) $op $pts
            set opwatch($pts,deg) $opdeg
            set opwatch($pts,op) $op
            foreach {type i j} $pts break
            if {$type eq "Q"} {
                set name v$i
            } else {
                set name h$j
                if {$i>1} {
                    append name ,[expr {$i-1}]
                }
            }
            set opwatch($pts,name) $name
            lappend opdegs $opdeg
        }
        set opwatch(degrees) [lsort -integer -unique $opdegs]

        proc ptsfilt {opdg poly} {
            variable opwatch
            if {![info exists opwatch($opdg)]} return
            set res {}
            steenrod::poly foreach $poly m {
                foreach {mo name} $opwatch($opdg) {
                    if {[steenrod::mono isabove $m $mo]
                        && [steenrod::mono isbelow $m $mo]} {
                        lappend res $name [steenrod::mono coeff $m]
                    }
                }
            }
            return $res
        }

        my db function chptsfilt [namespace current]::ptsfilt

        # default line subscriptions unless we have a better default
        set lines {}
        # default: display first three line types
        foreach dg [lrange $opwatch(degrees) 0 3] dash {
            {normal {}} {normal {}} {normal {}} {normal -}
        } {
            if {$dg eq ""} continue
            foreach {o n} $opwatch($dg) {
                lappend lines $n
                set cfg(line-$n-dash) $dash
                set cfg(line-$n-width) 1
            }
        }
        set cfg(lines-subscribed) $lines
        set cfg(lines-read) {}
        trace add variable [namespace current]::cfg(lines-subscribed) write \
            "[list [self] reload cleardots false loaddots false clearlines unsubscribed] ;#"
    }

    method opinfo {} {
        array get opwatch
    }

    method busymsg {msg script} {
        set cfg(_progdlg_) .prog[incr ::progcnt]
        ProgressDlg $cfg(_progdlg_) -title $msg -parent $widgets(cvs) \
            -variable [my cfgvar _progcnt_] \
            -textvariable [my cfgvar _progmsg_] -type infinite -maximum 2500
        set rc [catch {
            uplevel 1 $script
        } err]
        set einf $::errorInfo
        destroy $cfg(_progdlg_)
        return -code $rc $err -errorInfo $einf
    }

    method progress {msg} {
        set cfg(_progmsg_) $msg
        incr cfg(_progcnt_)
    }

    method Untraced {varname script} {
        upvar 1 $varname v
        set ti [trace info variable v]
        foreach x $ti {
            trace remove variable v {*}$x
        }
        uplevel 1 $script
        foreach x $ti {
            trace add variable v {*}$x
        }
    }

    method make-axes {} {
        set ndgs [expr {$cfg(maxn)-$cfg(minn)}]
        set sdgs [expr {$cfg(maxs)-$cfg(mins)}]
        set mmpd [expr {1000.0/$cfg(dpm)}]

        foreach {x1 y1 x2 y2} [my cvs cget -scrollregion] break
        my xax configure -scrollregion [list $x1 0 $x2 1]
        my yax configure -scrollregion [list 0 $y1 1 $y2]

        set fnt $cfg(axisfont)
        # measure the font height

        set bbox1 [my xax bbox [my xax create text 0 0 -text $sdgs -font $fnt]]
        set bbox2 [my xax bbox [my xax create text 0 0 -text $ndgs -font $fnt]]

        set w [expr {[lindex $bbox1 2]-[lindex $bbox1 0]}]
        set h [expr {[lindex $bbox2 3]-[lindex $bbox2 1]}]

        my xax configure -height [expr {$h+6}]
        my yax configure -width  [expr {$w+6}]

        set xoff [expr {$w+3}]
        set yoff [expr {$h/2.0+3}]

        # try to get roughly 100 ticks per meter  / x-axis first
        set numticks [expr {$ndgs / (1.0*$cfg(dpm)) * 100.0}]
        set tickspacing [expr {$ndgs / $numticks}]

        unset -nocomplain tsp
        foreach quant {1 2 5 10 20 50 100} {
            if {$tickspacing < $quant} {
                set tsp $quant
                break
            }
        }
        if {![info exists tsp]} {
            set tsp [expr {round(100*round($tickspacing/100.0))}]
        }

        my xax delete all
        for {set x 0} {$x<=$cfg(maxn)} {incr x $tsp} {
            my xax create text [expr {$mmpd*$x}]m $yoff -justify center -text $x -font $fnt
        }
        for {set x -$tsp} {$x>=$cfg(minn)} {incr x -$tsp} {
            my xax create text [expr {$mmpd*$x}]m $yoff -justify center -text $x -font $fnt
        }

        # same for y-axis

        set numticks [expr {$sdgs / (1.0*$cfg(dpm)/(1.0*$cfg(y2x))) * 100.0}]
        set tickspacing [expr {$sdgs / $numticks}]

        unset -nocomplain tsp
        foreach quant {1 2 5 10 20 50 100} {
            if {$tickspacing < $quant} {
                set tsp $quant
                break
            }
        }
        if {![info exists tsp]} {
            set tsp [expr {round(100*round($tickspacing/100.0))}]
        }

        my yax delete all
        for {set x 0} {$x<=$cfg(maxs)} {incr x $tsp} {
            my yax create text $xoff [expr {-$mmpd*$x*$cfg(y2x)}]m -justify right \
                -text $x -anchor e -font $fnt
        }
        for {set x -$tsp} {$x>=$cfg(mins)} {incr x -$tsp} {
            my yax create text $xoff [expr {-$mmpd*$x*$cfg(y2x)}]m -justify right \
                -text $x -anchor e -font $fnt
        }

    }

    method reload {args} {

        my busymsg "Loading..." {

            array set opts {
                loaddots yes
                loadlines yes
                cleardots yes
                clearlines all
            }
            array set opts $args

            my db eval {
                select max(sdeg)+0.5 as maxs, min(sdeg)-0.5 as mins,
                max(ndeg)+0.5 as maxn, min(ndeg)-0.5 as minn,
                count(*) as numgens from chart_generators
            } cfg break

            if {$cfg(maxn) eq ""} {set cfg(maxn) 1}
            if {$cfg(maxs) eq ""} {set cfg(maxs) 1}
            if {$cfg(minn) eq ""} {set cfg(minn) 0}
            if {$cfg(mins) eq ""} {set cfg(mins) 0}

            if {$cfg(dpm) eq ""} {
                # guess a reaonable value for dpm
                set dims [my db eval {
                    select distinct ndeg from chart_generators order by ndeg asc limit 10
                }]
                if {[llength $dims]} {
                    set spread [expr {[lindex $dims end]-[lindex $dims 0]}]
                } else {
                    set spread 0
                }
                if {$spread == 0} {set spread 1}
                set cfg(dpm) [expr {round(10*$spread)}]
            }
            if {$cfg(y2x) eq ""} {
                set cfg(y2x) 1.0
            }

            if {$opts(cleardots)} {
                my db eval {
                    delete from dots;
                }
                my cvs delete dot
            }

            if {$opts(clearlines) ne "none"} {
                set where {}
                set what {}
                if {$opts(clearlines) eq "unsubscribed"} {
                    set inlist {}
                    foreach l $cfg(lines-subscribed) {
                        lappend inlist '$l'
                    }
                    set where " where type not in ([join $inlist ,])"
                    set newread {}
                    foreach x $cfg(lines-read) {
                        if {[lsearch -exact $cfg(lines-subscribed) $x] >= 0} {
                            lappend newread $x
                        } else {
                            lappend what line-$x
                        }
                    }
                    set cfg(lines-read) $newread
                } else {
                    set what line
                    set cfg(lines-read) {}
                }
                my db eval "delete from lines $where;"
                my cvs delete {*}$what
            }
            set gprogmsk [expr {int($cfg(numgens)/20.0)}]
            if {$gprogmsk > 200} {set gprogmsk 200}
            if {$gprogmsk<1} {set gprogmsk 1}
            set lines-needed {}
            set degrees_needed {}
            foreach l $cfg(lines-subscribed) {
                if {[lsearch -exact $cfg(lines-read) $l] < 0} {
                    lappend lines-needed $l
                    lappend degrees_needed $opwatch($l,deg)
                }
                if {![info exists cfg(line-$l-dash)]} {
                    set cfg(line-$l-dash) {normal -..}
                    set cfg(line-$l-width) 1
                }
            }
            set cfg(linesql) [subst -novariables {
                select targen, opideg,
                chptsfilt(opideg,data) as ptsinfo
                from chart_fragments where srcgen=$genid and
                opideg in ([join [set degrees_needed] ,])
            }]
            my progress "Checking crowdiness..."
            array set crowdiness [my db eval {
                select ndeg, max(dim)
                from (select sdeg,ndeg,count(*) as dim from chart_generators
                      group by sdeg,ndeg)
                group by ndeg
            }]

            set mmpd [expr {1000.0/$cfg(dpm)}]
            set xma [expr {$cfg(maxn)*$mmpd}]m
            set ymi [expr {-$cfg(maxs)*$mmpd*$cfg(y2x)}]m
            set xmi [expr {$cfg(minn)*$mmpd}]m
            set yma [expr {-$cfg(mins)*$mmpd*$cfg(y2x)}]m
            my cvs configure -scrollregion [list $xmi $ymi $xma $yma]
            my make-axes
            if {$cfg(placementmode) eq "bydim"} {
                set xexpr {$ndeg+0.3-0.6*((1+$basid)/(1.0*(1+$dim)))}
                set yexpr {$sdeg-0.3+0.6*((1+$basid)/(1.0*(1+$dim)))}
            } else {
                set xexpr {$ndeg+$coff*(1-2*$basid/($crdix-1.0))}
                set yexpr {$sdeg-0.5*$coff*(1-2*$basid/($crdix-1.0))}
            }
            my db eval {
                select distinct sdeg, ndeg, count(*) as dim from chart_generators
                group by sdeg, ndeg order by sdeg,ndeg
            } {
                set crdi $crowdiness($ndeg)
                set coff [expr {0.3*(1-exp(1-$crdi))}]
                set crdix [expr {$crdi>1 ? $crdi : 2}]
                my db eval {
                    select rowid, basid, edeg from chart_generators
                    where sdeg=$sdeg and ndeg=$ndeg
                } {
                    #puts box($sdeg,$ndeg)
                    set xl [expr $xexpr]
                    set yl [expr $yexpr]
                    set x [expr {$xl*$mmpd}]
                    set y [expr {-$yl*$mmpd*$cfg(y2x)}]
                    set filt [expr $cfg(_fexpr_)]
                    set col [my Filtcol $filt]
                    if {$opts(loaddots)} {
                        set id [my cvs create image ${x}m ${y}m \
                                    -image [my Dot $filt] -tags [list dot filt$filt] \
                                    -activeimage [my Dot active]]
                        my db eval {
                            insert into dots(cvsid,genid,x,y,filt)
                            values($id,$rowid,$xl,$yl,$filt)
                        }
                    }
                    if {$opts(loadlines)} {
                        set genid $rowid
                        my db eval $cfg(linesql) {
                            if {[llength $ptsinfo]} {
                                set tarid [my db onecolumn {
                                    select cvsid from dots
                                    where genid=$targen
                                }]
				if {$tarid eq ""} {
				    # line hits a generator outside of the region that we currently display
				    continue
				}
                                #puts srcgen=$rowid,targen=$targen,tarid=$tarid,ptsinfo=$ptsinfo
                                set tc [my cvs coords $tarid]
                                foreach {nm coeff} $ptsinfo {
                                    set lid [my cvs create line ${x}m ${y}m {*}$tc \
                                                 -tags [list line-$nm line filt$filt] -fill $col \
                                                 -dash [lindex $cfg(line-$nm-dash) 1] \
                                                 -state [lindex $cfg(line-$nm-dash) 0] \
                                                 -width $cfg(line-$nm-width) \
                                                 -activewidth 2 -activefill $cfg(activefg)]
                                    my db eval {
                                        insert into lines(cvsid,srcgen,targen,coeff,type)
                                        values($lid,$genid,$targen,$coeff,$nm);
                                    }
                                }
                            }
                        }
                    }
                    if {[incr gcnt] % $gprogmsk == 0} {
                        set perc [expr {100.0*$gcnt/(1.0*(0.001+$cfg(numgens)))}]
                        my progress [format "Generators read: %d (%.0f%%)" $gcnt $perc]
                    }
                }
            }
            set cfg(lines-read) $cfg(lines-subscribed)
            # TODO: stack order should depend on filtration display style
            my db eval {select distinct filt from dots order by filt asc} {
                my cvs lower filt$filt
            }
            my cvs lower line
        }
    }

    method Filtcol {style {clearCache no}} {
        if {$clearCache} {
            unset -nocomplain colcache
        }
        if {![info exists colcache($style)]} {
            if {$style eq "active"} {
                set colcache(active) $cfg(activefg)
            } else {
                set x [expr {1-exp(.15*-$style)}]

                set r [expr {round($x*$cfg(fcol1r)+(1-$x)*$cfg(fcol0r))}]
                set g [expr {round($x*$cfg(fcol1g)+(1-$x)*$cfg(fcol0g))}]
                set b [expr {round($x*$cfg(fcol1b)+(1-$x)*$cfg(fcol0b))}]

                set r [expr {max(min($r,255),0)}]
                set g [expr {max(min($g,255),0)}]
                set b [expr {max(min($b,255),0)}]

                set colcache($style) [format "\#%02x%02x%02x" $r $g $b]
            }
        }
        return $colcache($style)
    }

    method dotimages {} {array names images *::dot<*}
    method linestyles {} {
        set res {}
        foreach nm $cfg(lines-subscribed) {
            set aux(name) $nm
            set aux(dash) [lindex $cfg(line-$nm-dash) 1]
            set aux(state) [lindex $cfg(line-$nm-dash) 0]
            set aux(width) $cfg(line-$nm-width)
            if {$aux(state) ne "hidden"} {
                lappend res [array get aux]
            }
        }
        return $res
    }
    method find-overlapping {xmin ymin xmax ymax} {
        set mmpd [expr {1000.0/$cfg(dpm)}]
        return [my cvs find overlapping \
                    [expr {$xmin*$mmpd}]m \
                    [expr {-$ymax*$mmpd*$cfg(y2x)}]m \
                    [expr {$xmax*$mmpd}]m \
                    [expr {-$ymin*$mmpd*$cfg(y2x)}]m ]
    }

    method Dot {style} {
        set name [self]::dot<$style>
        if {![info exist images($name)]} {
            set images($name) $name
            image create bitmap $name -data [dict get [set $cfg(dotbitmap)] data]
            $name configure -foreground [my Filtcol $style]
        }
        return $images($name)
    }

    method new-dotbitmap {} {
        foreach name [my dotimages] {
            regexp {dot<([^>]*)>} $name -> style
            image create bitmap $name -data [dict get [set $cfg(dotbitmap)] data]
            $name configure -foreground [my Filtcol $style]
        }
    }

    method new-filtcols {{update yes}} {
        scan $cfg(filtcol-0) %c%02x%02x%02x x \
            cfg(fcol0r) cfg(fcol0g) cfg(fcol0b)
        scan $cfg(filtcol-1) %c%02x%02x%02x x \
            cfg(fcol1r) cfg(fcol1g) cfg(fcol1b)
        unset -nocomplain colcache
        foreach img [array names images dot*] {
            set style [lindex [split $img -] 1]
            $img configure -foreground [my Filtcol $style]
        }
        my xax itemconfigure all -fill [my Filtcol 0]
        my yax itemconfigure all -fill [my Filtcol 0]
        my new-filtstyle $update
    }

    method new-filtstyle {{update yes}} {
        if {$cfg(filtstyle) eq "novikov"} {
            set cfg(_fexpr_) {$sdeg-$edeg}
        } elseif {$cfg(filtstyle) eq "bockstein"} {
            set cfg(_fexpr_) {$edeg}
        } else {
            set cfg(_fexpr_) 0
        }
        if {!$update} return
        my busymsg "Updating..." {
            my db eval {
                select d.cvsid as cvsid, g.sdeg as sdeg, g.edeg as edeg
                from dots as d join chart_generators as g
                on d.genid = g.rowid
            } {
                set filt [expr $cfg(_fexpr_)]
                my cvs itemconfigure $cvsid -image [my Dot $filt]
                my db eval {
                    update dots set filt=$filt where cvsid = $cvsid
                }
                if {([incr pcnt]&0xff) == 1} {my progress "Updating dots..."}
             }
            my db eval {
                select l.cvsid as cvsid, d.filt as filt
                from lines as l join dots as d
                on l.srcgen = d.genid
            } {
                my cvs itemconfigure $cvsid -fill [my Filtcol $filt]
                if {([incr pcnt]&0xff) == 1} {my progress "Updating lines..."}
            }
        }
    }

    method new-dpm {} {
        my busymsg "Updating..." {
            set xv [my cvs xview]
            set yv [my cvs yview]

            set mmpd [expr {1000.0/$cfg(dpm)}]
            set xma [expr {$cfg(maxn)*$mmpd}]m
            set ymi [expr {-$cfg(maxs)*$mmpd*$cfg(y2x)}]m
            set xmi [expr {$cfg(minn)*$mmpd}]m
            set yma [expr {-$cfg(mins)*$mmpd*$cfg(y2x)}]m

            my cvs configure -scrollregion [list $xmi $ymi $xma $yma]
            my xax configure -scrollregion [list $xmi 0 $xma 1]
            my yax configure -scrollregion [list 0 $ymi 1 $yma]
            my make-axes
            my xview moveto [lindex $xv 0]
            my yview moveto [lindex $yv 0]
            update idletasks

            my db eval {
                select cvsid,x as xl,y as yl from dots
            } {
                set x [expr {$xl*$mmpd}]
                set y [expr {-$yl*$mmpd*$cfg(y2x)}]
                my cvs coords $cvsid ${x}m ${y}m
                if {([incr pcnt]&0xff) == 1} {my progress "Updating dots..."}
            }

            my db eval {
                select l.cvsid as lid, s.cvsid as src, t.cvsid as tar
                from lines as l
                join dots as s on l.srcgen = s.genid
                join dots as t on l.targen = t.genid
            } {
                my cvs coords $lid {*}[my cvs coords $src] {*}[my cvs coords $tar]
                if {([incr pcnt]&0xff) == 1} {my progress "Updating lines..."}
            }
        }
    }
}

oo::class create subscrdlg {

    variable dlg cb subscriptions

    constructor {parent opinfo subinfo callback} {

        array set subscriptions $subinfo
        array set opwatch $opinfo
        set cb $callback

        set dlg [Dialog .sdlg[incr ::subscrcnt] -parent $parent -title "Line Subscriptions"]

        set f [$dlg getframe]
        ttk::labelframe $f.p -text "Available line types:"

        foreach deg $opwatch(degrees) {
            foreach {op pts} $opwatch($deg) {
                if {$pts eq "unit"} continue
                set j 0
                foreach {type i j} $pts break
                if {$type eq "Q"} {
                    set j -1
                    incr i
                }
                set name $opwatch($pts,name)
                set w [string tolower $f.p.x${i}x${j}]
                set var [namespace current]::subscriptions($pts)
                ttk::checkbutton $w -text $name -variable $var
                grid configure $w -row [expr {10-$j}] -column $i -sticky news
            }
        }
        pack $f.p -expand 0 -fill both

        $dlg add -text Ok -command [list Dialog::enddialog $dlg ok]
        $dlg add -text Apply -command [list [self] apply]
        $dlg add -text Cancel -command [list Dialog::enddialog $dlg cancel]
    }
    method apply {} {
        eval $cb [list [array get subscriptions]]
    }
    method run {} {
        if {[$dlg draw] eq "ok"} {
            my apply
        }
        destroy $dlg
    }
}

oo::class create textwdg {
    variable wdg
    constructor {path title args} {
        ttk::labelframe $path -text $title
        text [set wdg(txt) $path.txt] -width 60 -height 7 -background white
        $wdg(txt) configure {*}$args
        ttk::scrollbar  [set wdg(scv) $path.scv] -orient vertical -command [list $wdg(txt) yview]
        ttk::scrollbar  [set wdg(sch) $path.sch] -orient horizontal -command [list $wdg(txt) xview]
        $wdg(txt) configure -xscrollcommand [list $wdg(sch) set]
        $wdg(txt) configure -yscrollcommand [list $wdg(scv) set]
        grid configure $wdg(txt) -row 1 -column 1 -sticky news
        grid configure $wdg(scv) -row 1 -column 2 -sticky news
        #grid configure $wdg(sch) -row 2 -column 1 -sticky news
        grid rowconfigure $path 1 -weight 1
        grid columnconfigure $path 1 -weight 1
        return $path
    }
    method txt {} {return $wdg(txt)}
    method get {} {$wdg(txt)  get 1.0 end}
}

oo::class create sqlconsole {
    variable db path wdg sql sqlfont
    constructor {dbcmd} {
        set db $dbcmd
        while {[winfo exists [set path .sqlcon[incr ::sqlconcnt]]]} {
            # try again
        }
        toplevel $path
        wm title $path "SQL Console"

        pack [ttk::panedwindow [set pane $path.pane] -orient vertical] -expand 1 -fill both
        set path $pane

        set sqlfont Courier
        yacop::prefdb trace sqlconsole sqlfont [namespace current]::sqlfont

        $pane add [ttk::frame $path.f1] -weight 2
        textwdg create sql $path.f1.sql "SQL" -font $sqlfont -height 5
        pack $path.f1.sql -expand 1 -fill both -padx 3 -pady 2
	pack [ttk::frame $path.f1.buttons] -side top -anchor w -padx 3 -pady 3 -fill y
        pack [ttk::button $path.f1.buttons.exec -text "Execute" -command [list [self] execute]] \
            -side left -anchor w -padx 3 -pady 3
        pack [ttk::button $path.f1.buttons.tabinf -text "Table Info" -command [list [self] tableinfo]] \
            -side left -anchor w -padx 3 -pady 3

        $pane add [ttk::frame $path.f2] -weight 3
        textwdg create res $path.f2.res "Result" -font $sqlfont -height 15 -state disabled
        pack $path.f2.res -expand 1 -fill both -padx 3 -pady 2
        set wdg(sql) [sql txt]
        set wdg(res) [res txt]

        set sql ""
        yacop::prefdb trace sqlconsole sql [namespace current]::sql
        $wdg(sql) insert 1.0 $sql
    }
    method execute {} {
        set sql [$wdg(sql) get 1.0 end]

        $wdg(res) configure -state normal
        $wdg(res) delete 1.0 end
        set rows 0
        yacop::timer start
        set ph [$db progress]
        $db progress $::yacop::dbprogsteps ""
        set nv [$db nullvalue]
        $db nullvalue NULL
        set rc [catch {
            $db eval $sql x {
                incr rows
                if {![info exists hdr]} {
                    set hdr [join $x(*) \t]
                    $wdg(res) insert end $hdr\n
                }
                set row {}
                foreach fld $x(*) {
                    lappend row $x($fld)
                }
                $wdg(res) insert end [join $row \t]\n
            }
        } err]
        $db nullvalue $nv
        $db progress $::yacop::dbprogsteps $ph
        if {$rc} {
            $wdg(res) insert 1.0 $err
        } else {
            set tm [yacop::timer stop]
            $wdg(res) insert end [format "\n%d rows returned in %.2f seconds" $rows $tm]
        }

        $wdg(res) configure -state disabled
        $wdg(res) xview moveto 0
        $wdg(res) yview moveto 0
    }
    method tableinfo {} {
        $wdg(res) configure -state normal
        $wdg(res) delete 1.0 end

	$wdg(res) insert end "List of tables and views:\n"

	$db eval {select type, name from sqlite_master where type in ('table', 'view') order by name} {
	    set inf "\n$type $name:\n"
	    $db eval "pragma table_info($name)" t {
		append inf [format "  %-10s  %s\n" $t(name) $t(type)]
	    }
	    $wdg(res) insert end $inf
	}

	set dbs "\ndatabases:"
	$db eval {pragma database_list} h {
	    append dbs [format "\n  %-10s: %s" $h(name) $h(file)]
	}
	$wdg(res) insert end $dbs
    }
}

oo::class create ValueDlg {
    variable dlg value
    constructor {parent vardesc initval} {

        Dialog [set dlg .pcdlg[incr ::pccnt]] -parent $parent \
            -title "Enter new value" -default 1

        pack [ttk::labelframe $dlg.f -text "New Value:"] -expand 1 -fill both -padx 4 -pady 4
        ttk::label $dlg.f.l -text "$vardesc: "
        ttk::entry $dlg.f.e -textvariable [namespace current]::value -width 5
        set value $initval
        grid configure $dlg.f.l -row 1 -column 1 -sticky news
        grid configure $dlg.f.e -row 1 -column 2 -sticky news
        grid columnconfigure $dlg 2 -weight 1

        pack [ttk::frame $dlg.bf] -side top -expand 0 -fill both

        $dlg add -text "Ok" -command \
            "[list Dialog::enddialog $dlg] \[set [namespace current]::value\]"
        $dlg add -text "Cancel" -command [list Dialog::enddialog $dlg ""]
    }
    method run {} {
        $dlg draw
    }
}

oo::class create charttoolbar {
    variable wdg chart cfg opwatch subscriptions
    constructor {path chartcvs} {
        set chart $chartcvs
        set wdg(tb) $path

        array set cfg {
            menuopts {}
        }

        my menubutton m -text Chart {
            $m add command -label "Open" -command [list [self] open] -accelerator "Ctrl O"
            $m add command -label "Reload" -command [list [self] reload] -accelerator "Ctrl R"
            $m add separator
            $m add command -label "Print" -command [list [self] print] -accelerator "Ctrl P"
            $m add command -label "SQL-Console" -command [list [self] sql] -accelerator "Ctrl S"
            $m add separator
            $m add command -label "Exit" -command [list [self] close] -accelerator "Ctrl X"
        }

        my space

        my menubutton m -text Appearance {
            my submenu x $m -label Colors {
                foreach {varname desc} {
                    canvasbg  {Canvas background}
                    activefg  {Canvas highlight}
                    filtcol-0 {Filtration (low)}
                    filtcol-1 {Filtration (high)}
                    lensebg   {Magnifier background}
                    infowinbg {Ballon background}
                    infowinfg {Ballon foreground}
                } {
                    $x add command -label $desc \
                        -command [list [self] chooseColor [$chart cfgvar $varname] $desc]
                }
            }
            my submenu x $m -label Fonts {
                foreach {varname desc} {
                    axisfont {Axis label}
                    textfont {Annotations}
                    sqlfont  {SQL console}
                } {
                    $x add command -label $desc \
                        -command [list [self] chooseFont [$chart cfgvar $varname] $desc]
                }
            }
            my submenu x $m -label "Dot Shapes" {
                foreach k [lsort [array names ::bitmaps]] {
                    set var ::bitmaps($k)
                    set name [dict get [set $var] name]
                    $x add radiobutton -label $name \
                        -variable [$chart cfgvar dotbitmap] -value $var
                }
            }
        }

        my space

        my menubutton m -text "Layout" {
            my submenu x $m -label "Dots/Meter" {
                $x add command -label "Zoom In" -accelerator "Ctrl +" \
                    -command [list $chart zoom [expr {exp(log(2)/3)}]]
                $x add command -label "Zoom Out" -accelerator "Ctrl -" \
                    -command [list $chart zoom [expr {exp(-log(2)/3)}]]
                $x add command -label "Set value" -accelerator "Ctrl D" \
                    -command [list [self] set-dpm]
            }
            my submenu x $m -label "Y-X-Scale" {
                $x add command -label "grow" -accelerator "Ctrl PgUp" \
                    -command [list $chart zoom 1 1.1]
                $x add command -label "shrink" -accelerator "Ctrl PgDwn" \
                    -command [list $chart zoom 1 [expr {1.0/1.1}]]
                $x add command -label "Set value" -accelerator "Ctrl Y" \
                    -command [list [self] set-y2x]
            }
            my submenu x $m -label "Viewtype" {
                foreach val [$chart db eval {select name from chart_viewtypes order by name}] {
                    $x add radiobutton -label $val \
                        -variable [$chart cfgvar viewtype] -value $val
                }
            }
            my submenu x $m -label "Filtration" {
                foreach val {novikov bockstein none} {
                    $x add radiobutton -label [string totitle $val] \
                        -variable [$chart cfgvar filtstyle] -value $val
                }
            }
            $m add command -label "Magnifier" -command [list [self] config-lense]
        }

        my space

        array set opwatch [$chart opinfo]
        array set subscriptions {}
        foreach l [set [$chart cfgvar lines-subscribed]] {
            set subscriptions($l) 1
        }

        my menubutton m -text "Lines" {
            $m add command -label "Subscriptions" -command [list [self] subscr-dlg]
            my submenu x $m -label "Display styles" {
                $x configure -postcommand [list [self] add-styles-menu $x]
            }
        }

        foreach m $wdg(menus) {
            set n [$m index last] ;# $n can be "none" on MacOS
            for {set i 0} {[string is integer $n] && $i<=$n} {incr i} {
                catch {
                    set acc [$m entrycget $i -accelerator]
                    set mod ""
                    if {[regexp Ctrl $acc]} {
                        set mod Control-
                        $m entryconfigure $i -accelerator [join $acc -]
                    }
                    set key [string map {
                        pgup Prior
                        pgdwn Next
                        + plus
                        - minus
                    } [string tolower [lindex $acc end]]]
                    bind [winfo toplevel $path] <$mod$key> +[list $m invoke $i]
                }
            }
        }
    }
    method set-dpm {} {
        catch {rename vdlg {}}
        ValueDlg create vdlg [$chart cvs] "dims/meter" [set [$chart cfgvar dpm]]
        set newval [vdlg run]
        catch {rename vdlg {}}
        if {$newval eq "" || ![string is double $newval] || $newval<0} return
        $chart set-dpm $newval [set [$chart cfgvar y2x]]
    }
    method set-y2x {} {
        catch {rename vdlg {}}
        ValueDlg create vdlg [$chart cvs] "y/x ratio" [set [$chart cfgvar y2x]]
        set newval [vdlg run]
        catch {rename vdlg {}}
        if {$newval eq "" || ![string is double $newval] || $newval<0} return
        $chart set-dpm [set [$chart cfgvar dpm]] $newval
    }
    method foreach-line {line script} {
        upvar 1 $line l
        foreach dg $opwatch(degrees) {
            foreach {op pts} $opwatch($dg) {
                if {[info exists subscriptions($pts)] && $subscriptions($pts)} {
                    set l $pts
                    uplevel 1 $script
                }
            }
        }
    }
    method add-styles-menu {m} {
        $m delete 0 end
        foreach what {dash width} {
            if {$what ne "dash"} {$m add separator}
            my foreach-line l {
                set name $opwatch($l,name)
                if {$what eq "dash"} {
                    my submenu y $m -label "dash: $name" {
                        foreach {nm dash} {
                            hide {hidden {}}
                            solid {normal {}}
                            dashed {normal -}
                            dotted {normal .}
                            dashdot {normal -.}
                            dashdot2 {normal -..}
                        } {
                            $y add radiobutton -label "$nm" \
                                -variable [$chart cfgvar line-$l-dash] \
                                -value $dash
                        }
                    }
                } else {
                    my submenu y $m -label "width: $name" {
                        foreach wdth {1 2 3 4} {
                            $y add radiobutton -label "$wdth pixel" \
                                -variable [$chart cfgvar line-$l-width] \
                                -value $wdth
                        }
                    }
                }
            }
        }
    }

    method subscr-dlg {} {
        subscrdlg create hmm [$chart cvs] [$chart opinfo] [array get subscriptions] \
            "[list [self] new-subscriptions]"
        hmm run
        rename hmm ""
    }
    method new-subscriptions {dictval} {
        array set subscriptions $dictval
        set sl {}
        foreach {l v} [array get subscriptions] {
            if {$v} {
                lappend sl $l
            }
        }
        set [$chart cfgvar lines-subscribed] $sl
    }

    method reload {{confirm no}} {
        if {$confirm} {
            if {"ok" ne [tk_messageBox -parent [$chart cvs] -default cancel \
                             -type okcancel -message "Reload data?" \
                             -icon question]} return
        }
        $chart reload
    }
    method print {} {
        if {[info exists ::env(YACOP_PRINT_DEV)]} {
            namespace eval :: [list source [info script]]
        }
        catch {rename dlg ""}
        PostscriptDlg create dlg $chart
        dlg run
    }
    method forever {} {
        return [namespace current]::forever
    }
    method close {{confirm yes}} {
        if {$confirm} {
            if {"ok" ne [tk_messageBox -parent [$chart cvs] -default cancel \
                             -type okcancel -message "Close this window?" \
                             -icon question]} return
        }
        set [my forever] true
    }
    method sql {} {
        set sco [sqlconsole new [$chart db]]
    }

    method space {{x 3}} {
        pack [ttk::frame [my newid]] -padx $x -side left
    }
    method submenu {subvar parent args} {
        upvar 1 $subvar sub
        set sub $parent.sub[llength [winfo children $parent]]
        lappend wdg(menus) $sub
        menu $sub {*}$cfg(menuopts)
        $parent add cascade -menu $sub {*}[lrange $args 0 end-1]
        uplevel 1 [lindex $args end]
    }
    method menubutton {var args} {
        upvar 1 $var menupath
        set p [my newid]
        set menupath $p.menu
        set mbt [ttk::menubutton $p -style Toolbutton \
                     {*}[lrange $args 0 end-1] -menu $menupath]
        pack $mbt -side left
        menu $menupath -tearoff 0 {*}$cfg(menuopts)
        lappend wdg(menus) $menupath
        uplevel 1 [lindex $args end]
    }
    method newid {} {
        return $wdg(tb).w[incr wdg(count)]
    }
    method separator {} {
        set sep [ttk::separator [my newid] -orient vertical]
        pack $sep -padx 3 -fill both -side left
    }
    method chooseColor {varname desc} {
        set col [SelectColor::dialog .coldlg -parent .main -color [set $varname] -title $desc]
        if {$col ne ""} {
            # transform "#a7adffffd04e" to "#a7ffd0"
            if {[string length $col] == 13} {
                set col "#[string range $col 1 2][string range $col 5 6][string range $col 9 10]"
            }
            set $varname $col
        }
    }

    method chooseFont {varname desc} {
        SelectFont::loadfont
        set col [SelectFont .fntdlg -parent .main -sampletext "What about g(2,126)?" -querysystem 1 -font [set $varname]  -title $desc]
        if {$col ne ""} {
            set $varname $col
        }
    }

}

oo::class create chartstatusbar {
    variable chart wdg
    constructor {path chartcvs} {
        set wdg(tb) $path
        set chart $chartcvs
        foreach var {
            prime
            algebra
            y2x
            dpm
            numgens
        } {
            set myvar [namespace current]::wdg(display-$var)
            pack [ttk::label [my newid] -textvariable $myvar -borderwidth 0 -relief flat] -pady 3 -padx 3 -side right
            trace add variable [$chart cfgvar $var] write "[list [self] new-$var] ;#"
            my new-$var
            my separator
        }
    }
    method newid {} {
        return $wdg(tb).w[incr wdg(count)]
    }
    method separator {} {
        set sep [ttk::separator [my newid] -orient vertical]
        pack $sep -padx 3 -fill both -side right
    }
    method new-prime {} {
        set wdg(display-prime) [format "prime: %s" [set [$chart cfgvar prime]]]
    }
    method new-dpm {} {
        set wdg(display-dpm) [format "%s dims/meter" [set [$chart cfgvar dpm]]]
    }
    method new-y2x {} {
        set wdg(display-y2x) [format "y/x: %.1f" [set [$chart cfgvar y2x]]]
    }
    method new-algebra {} {
        set a [set [$chart cfgvar algebra]]
        foreach {ext red} $a break
        set wdg(display-algebra) "algebra: ext $ext red [join $red -]"
    }
    method new-numgens {} {
        set wdg(display-numgens) [format "%s generators" [set [$chart cfgvar numgens]]]
    }
}

oo::class create ChartViewer {
    variable top chart db forever
    constructor {path dbcmd filename} {
        set top $path
        ttk::frame $top
        set chart [namespace current]::$top.chartobj
        chartcvs create $chart $top.chartcvs $dbcmd
        ttk::frame $top.toolbar -relief raised -borderwidth 2
        charttoolbar create ctb $top.toolbar $chart
        ttk::frame $top.status -relief raised -borderwidth 2
        chartstatusbar create cts $top.status $chart

        pack $top.toolbar -expand 0 -fill both
        pack $top.chartcvs -expand 1 -fill both
        pack $top.status -expand 0 -fill both
        $chart cvs configure -width 500 -height 300
    }
    method chart {args} {
        if {0 == [llength $args]} {
            return $chart
        }
        uplevel 1 [list $chart] $args
    }
    method forever {} {
        ctb forever
    }
    method run {{waitForever true}} {
        #wm protocol [winfo toplevel $top] WM_DELETE_WINDOW  "[list set [my forever] true] ;#"
        wm protocol [winfo toplevel $top] WM_DELETE_WINDOW  "[list [namespace current]::ctb close yes] ;#"
        wm deiconify [winfo toplevel $top]
        tkwait visibility $top
        after idle "[list $chart reload] ; [list $chart xview moveto 0] ; [list $chart yview moveto 1] ; "
        if {$waitForever} {
            vwait [my forever]
            destroy $top
        }
    }
    destructor {
        catch {destroy [winfo toplevel $top]}
    }
}

proc yacop::chartgui {dbcmd filename} {
    namespace eval :: {
        package require Tk 8.6
        package require BWidget 1.9.10

        switch -- $::tcl_platform(platform) {
            windows {
                ttk::style theme xpnative
            }
            default {
                if {[catch {
                    ttk::style theme use aqua
                }]} {
                    ttk::style theme use clam
                }
            }
        }
    }
    while {[winfo exists [set path .chgui[incr ::yacop::chguicnt]]]} {
        # try again
    }
    toplevel $path
    set title "Yacop chart"
    if {$filename ne ":memory:"} {
        append filename " ($filename)"
    }
    wm title $path $title
    set chv [ChartViewer new $path.chv $dbcmd $filename]
    pack $path.chv -expand 1 -fill both
    $chv run false
    return $chv
}

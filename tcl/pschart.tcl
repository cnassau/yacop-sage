#
# PDF charts
#
# Copyright (C) 2009-2017 Christian Nassau <nassau@nullhomotopie.de>
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License version 2 as
# published by the Free Software Foundation.
#

package require pdf4tcl 0.9.1

catch {rename PostscriptDlg ""}
catch {rename PostscriptChart ""}
catch {rename PdfChart ""}

# media types from /etc/enscript.cfg
foreach {
    name width height llx lly urx ury
} {
    A3 842 1190 24 24 818 1166
    A4 595 842 24 24 571 818
    A5 420 595 24 24 396 571
    Legal 612 1008 24 24 588 984
    Letter 612 792 38 24 574 768
    A4dj 595 842 24 50 571 818
    Letterdj 612 792 24 40 588 768
    letter 612 792 24 24 574 768
    note 540 720 24 24 516 696
    legal 612 1008 24 24 588 984
    a0 2380 3368 24 24 2356 3344
    a1 1684 2380 24 24 1660 2356
    a2 1190 1684 24 24 1166 1660
    a3 842 1190 24 24 818 1166
    a4 595 842 24 24 571 818
    a5 421 595 24 24 397 571
    a6 297 421 24 24 273 397
    a7 210 297 24 24 186 273
    a8 148 210 24 24 124 186
    a9 105 148 24 24 81 124
    a10 74 105 24 24 50 81
    b0 2836 4008 24 24 2812 3984
    b1 2004 2836 24 24 1980 2812
    b2 1418 2004 24 24 1394 1980
    b3 1002 1418 24 24 978 1394
    b4 709 1002 24 24 685 978
    b5 501 709 24 24 477 685
    archE 2592 3456 24 24 2568 3432
    archD 1728 2592 24 24 1704 2568
    archC 1296 1728 24 24 1272 1704
    archB 864 1296 24 24 840 1272
    archA 648 864 24 24 624 840
    flsa 612 936 24 24 588 912
    flse 612 936 24 24 588 912
    halfletter 396 612 24 24 372 588
    11x17 792 1224 24 24 768 1200
    ledger 1224 792 24 24 1200 768
} {
    lappend media(names) $name
    foreach var {width height llx lly urx ury} {
        set media($name,$var) [set $var]
    }
    set media($name,effwidth) [expr {$media($name,urx)-$media($name,llx)}]
    set media($name,effheight) [expr {$media($name,ury)-$media($name,lly)}]
}

oo::class create PostscriptDlg {

    variable db dlg cfg wdg chart

    constructor {chartcvs} {

        set chart $chartcvs

        array set cfg {
            medium A4
            orient landscape
            dotsize 5
            circstyle hollow
            font "Times-Roman"
            fontsize 12
            showlines no
            delivery "save file"
            command {okular $filename}
            meter2pspoint 2834.645669291
        }

        foreach key {
            medium orient circstyle dotsize font fontsize showlines delivery command
        } {
            yacop::prefdb trace printdlg $key [namespace current]::cfg($key)
        }

        array set x [$chart getconfig]

        $chart db eval {
            select min(ndeg) as dimstart, max(ndeg) as dimstop,
            min(sdeg) as sdegstart, max(sdeg) as sdegstop from chart_generators
        } cfg break

        set cfg(filtstyle) $x(filtstyle)
        set cfg(startcol)  $x(filtcol-0)
        set cfg(endcol)    $x(filtcol-1)
        set cfg(y2x) $x(y2x)
        set cfg(dpm) $x(dpm)

        #trace add variable cfg write "[list [self] configchange]"

        # trigger re-calculation of dpp
        my configchange cfg medium write

        set dlg [Dialog .pcdlg[incr ::pccnt] -parent [$chart cvs] \
                     -title "Postscript Chart"]

	my MakeDialog
    }

    method configchange {name1 name2 op} {
        global media
        if {$name2 eq "medium" || $name2 eq "orient"} {
            # recompute dpp from page size and dpm
            if {$cfg(orient) ne "landscape"} {
                set pgsize $media($cfg(medium),effwidth)
            } else {
                set pgsize $media($cfg(medium),effheight)
            }
            set pgsizem [expr {$pgsize/$cfg(meter2pspoint)}]
            set cfg(dpp) [expr {round($pgsizem*$cfg(dpm))}]
        }
        if {$name2 eq "dpp"} {
            # recompute dpm from page size and dpp
            if {$cfg(orient) ne "landscape"} {
                set pgsize $media($cfg(medium),effwidth)
            } else {
                set pgsize $media($cfg(medium),effheight)
            }
            set pgsizem [expr {$pgsize/$cfg(meter2pspoint)}]
            set cfg(dpm) [expr {$cfg(dpp)/$pgsizem}]
        }
        if {$name2 eq "delivery"} {
            if {[regexp -nocase -- save $cfg(delivery)]} {
                $cfg(command-widget) configure -state disabled
            } else {
                $cfg(command-widget) configure -state normal
            }
        }
    }

    method run {} {
	$dlg draw
    }

    method MakeDialog {} {
        global media
	set f [$dlg getframe]

	my labelframe "Configuration" {
	    my slot s medium 1 1 "Papersize" {
		ttk::combobox $s -values [lsort [pdf4tcl::getPaperSizeList]] -width 9 -state readonly
	    }
	    my slot s dpp 1 2 "Dims/Page" {
		ttk::entry $s -width 5
	    }
	    my slot s orient 2 1 "Orientation" {
		ttk::combobox $s -values {portrait landscape} -width 9 -state readonly
	    }
	    my slot s y2x 2 2 "Y/X ratio" {
		ttk::entry $s -width 5
	    }
	    my separator 3
	    my slot s dimstart 4 1 "Dimension (min)" {
		ttk::entry $s -width 5
	    }
	    my slot s sdegstart 4 2 "Homological degree (min)" {
		ttk::entry $s -width 5
	    }
	    my slot s dimstop   5 1 "Dimension (max)" {
		ttk::entry $s -width 5
	    }
	    my slot s sdegstop  5 2 "Homological degree (max)" {
		ttk::entry $s -width 5
	    }
	    my separator 6
	    my slot s filtstyle 7 1 "Display 3rd grading" {
		ttk::combobox $s -width 9 -values {novikov bockstein none} -state readonly
	    }
	    image create bitmap [self]scol -data {
		#define a_width 11
		#define a_height 11
		#define a_x_hot 6
		#define a_y_hot 6
		static unsigned char a_bits[] = {
		    0x00, 0x00, 0xfe, 0x03, 0xfe, 0x03, 0xfe, 0x03, 0xfe, 0x03, 0xfe, 0x03,
		    0xfe, 0x03, 0xfe, 0x03, 0xfe, 0x03, 0xfe, 0x03, 0x00, 0x00
		};
	    } -foreground yellow -background black
	    image create bitmap [self]ecol -data {
		#define a_width 11
		#define a_height 11
		#define a_x_hot 6
		#define a_y_hot 6
		static unsigned char a_bits[] = {
		    0x00, 0x00, 0xfe, 0x03, 0xfe, 0x03, 0xfe, 0x03, 0xfe, 0x03, 0xfe, 0x03,
		    0xfe, 0x03, 0xfe, 0x03, 0xfe, 0x03, 0xfe, 0x03, 0x00, 0x00
		};
	    } -foreground red -background black
	    my slot s startcol-txt 7 2 "Color gradient" {
                ttk::frame $s
		pack [ttk::button $s.start -compound right -text from \
                          -image [self]scol -command [list [self] coledit $s.start] \
                          -style Toolbutton] -side left
		pack [ttk::button $s.stop -compound right -text to \
                          -image [self]ecol -command [list [self] coledit $s.stop] \
                          -style Toolbutton] -side left
	    }
            foreach {var img} {
                startcol scol
                endcol ecol
            } {
                set v [namespace current]::cfg($var)
                set i [self]$img
                trace add variable $v write \
                    "[list $i configure -foreground] \[set $v\] ;#"
                set $v [set $v]
            }
            my separator 8
            my slot s delivery 9 1 "Delivery" {
                ttk::combobox $s -values {
                    {execute command} {save file}
                } -width 12 -state readonly
            }
            my slot s command 9 2 "Command" {
                set cfg(command-widget) $s
                ttk::entry $s -width 12
            }
            set cfg(delivery) $cfg(delivery) ;# triggers command widget state update
            $dlg add -text "Create Chart" -command [list [self] getchart]
            $dlg add -text Close -command [list Dialog::enddialog $dlg 0]
	}
    }
    method getchart {} {
        if {[regexp xecut $cfg(delivery)]} {
            if {[file isdirectory /tmp]} {
                set fnm /tmp/yacop-chart-%s.ps
            } else {
                set fnm yacop-chart-%s.ps
            }
            while 1 {
                set f [format $fnm [expr {int(rand()*10000000000)}]]
                if {![file exists $f]} break
            }
        } else {
            set f [tk_getSaveFile -defaultextension ps -parent $dlg -filetypes {
                {{Pdf files} .pdf}
            } -initialfile chart.pdf ]
        }
        if {$f eq ""} return
        set f [file normalize $f]
        set pxx [PdfChart new $chart [array get cfg]]
        set data [$pxx getchart]
        $pxx destroy
        set ch [open $f w]
        fconfigure $ch -translation binary
        puts $ch $data
        close $ch
        if {[regexp xecut $cfg(delivery)]} {
            if {[catch {
                set cmd {exec -ignorestderr}
                foreach word $cfg(command) {
                    if {$word eq {$filename}} {
                        lappend cmd $f
                    } else {
                        lappend cmd $word
                    }
                }
                eval $cmd
            } err]} {
                tk_messageBox -type ok -icon error -message "Oops:\n\n $::errorInfo" -parent $dlg
            }
            catch {file delete $f}
        }
    }
    method coledit {button} {
        set imgname [$button cget -image]
        set col [SelectColor::dialog .coldlg -parent [$dlg getframe] \
                     -color [$imgname cget -foreground] -title "Choose a color"]
        if {$col ne ""} {
            $imgname configure -foreground $col
            # hack: requiered to update button display
            $button configure -image $imgname
        }
    }
    method labelframe {title script} {
	set f [$dlg getframe]
	set wdg(lf) [ttk::labelframe $f.l[incr wdg(cnt)] -text $title]
	pack $wdg(lf) -side top -expand 0 -fill both
	uplevel 1 $script
    }
    method separator {row} {
	grid configure [ttk::separator $wdg(lf).l[incr wdg(cnt)] \
                            -orient horizontal] -row $row -column 1 \
            -columnspan 20 -sticky news -pady 5
    }
    method slot {wvar cvar row col name script} {
	upvar 1 $wvar svar
	grid configure [ttk::label $wdg(lf).l[incr wdg(cnt)] -text "$name: "] \
	    -row $row -column [expr {3*$col}] -sticky w -padx 2 -pady 2 -ipadx 2 -ipady 2
	set svar $wdg(lf).l[incr wdg(cnt)]
	uplevel 1 $script
	catch {
	    # this fails for buttons
	    $svar configure -textvariable [namespace current]::cfg($cvar)
	}
        if {![catch {$svar cget -values}]} {
            # combobox: use trace on variable
            trace add variable cfg($cvar) write "[list [self] configchange]"
        } else {
            bind $svar <FocusOut> "[list [self] configchange cfg $cvar write]"
        }
	grid configure $svar -row $row -column [expr {3*$col+1}] -sticky w
	if {$col>1} {
	    grid columnconfigure $wdg(lf) [expr {3*$col-1}] -weight 1 -minsize 15
	}
    }


}

# ------------------------------------------------


oo::class create PostscriptChart {

    variable db chart output cfg medium cvsids

    constructor {chcvs cfgdict} {
        global media
	set chart $chcvs
        array set cfg $cfgdict

        foreach var {llx lly urx ury width height} {
            set medium($var) $media($cfg(medium),$var)
        }
	yacop::sqlite [set db [namespace current]::chdb] :memory:

	my db eval {
            create table pages
            (pageid integer primary key,
             minx double, maxx double, miny double, maxy double);

            create index pageidx on pages(minx,maxx,miny,maxy);
	}

        set h [expr {$medium(ury)-$medium(lly)}]
        set w [expr {$medium(urx)-$medium(llx)}]

        switch -- [string index $cfg(orient) 0] {
            l {
                set ptsperdim [expr {$h/(1.0*$cfg(dpp))}]
                set spp [expr {int($w/($ptsperdim*$cfg(y2x)))}]
            }
            p {
                set ptsperdim [expr {$w/(1.0*$cfg(dpp))}]
                set spp [expr {int($h/($ptsperdim*$cfg(y2x)))}]
            }
        }

        if {$spp<1} {
            error "config has less than one homological degree per page"
        }

        set cfg(spp) $spp
        set cfg(ptsperdim) $ptsperdim

        # register pages

        for {set i 0} {$cfg(dimstart)+$i*$cfg(dpp) <= $cfg(dimstop)} {incr i} {
            for {set j 0} {$cfg(sdegstart)+$j*$cfg(spp) <= $cfg(sdegstop)} {incr j} {
                set minx [expr {$cfg(dimstart)+$i*$cfg(dpp)}]
                set maxx [expr {$cfg(dimstart)+(1+$i)*$cfg(dpp)}]
                set miny [expr {$cfg(sdegstart)+$j*$cfg(spp)}]
                set maxy [expr {$cfg(sdegstart)+(1+$j)*$cfg(spp)}]
                set ids [$chart find-overlapping \
                             [expr {$minx-1}] [expr {$miny-1}] \
                             [expr {$maxx+1}] [expr {$maxy+1}]]
                if {[llength $ids]} {
                    my db eval {
                        insert into pages(minx,maxx,miny,maxy)
                        values($minx,$maxx,$miny,$maxy)
                    }
                    set cvsids([my db last_insert_rowid]) $ids
                }
            }
        }
    }

    method db {cmd args} {
	uplevel 1 [list $db $cmd] $args
    }

    method postscript {stuff} {
        set substuff [uplevel 1 [list subst $stuff]]
        foreach line [split $substuff \n] {
            set line [string trim $line]
            if {[string length $line]} {
                append output $line \n
            }
        }
    }

    method Parsecol {colspec} {
        if {[regexp -nocase -expanded {
            [\#]?([0-9a-f][0-9a-f])([0-9a-f][0-9a-f])([0-9a-f][0-9a-f])
        } $colspec total r g b]} {
            return [list [expr (0x$r)/255.0] [expr (0x$g)/255.0] [expr (0x$b)/255.0]]
        }
        error "color \"$colspec\" not understood"
    }

    method getchart {} {

        set output ""

        set portrait true
        set Orientation Portrait
        if {[string match l* $cfg(orient)]} {
            set Orientation Landscape
            set portrait false
        }

        foreach key {dpp spp ptsperdim y2x} {
            set $key $cfg($key)
        }

        # determine how to label the axes
        foreach {maskvar dimsperpagevar} {
            mskx dpp msky spp
        } {
            set $maskvar 1
            if {[set $dimsperpagevar] > 5} {
                set $maskvar 2
                if {[set $dimsperpagevar] > 15} {
                    set $maskvar 5
                    if {[set $dimsperpagevar] > 25} {
                        set $maskvar 10
                        if {[set $dimsperpagevar] > 100} {
                            set $maskvar 20
                            if {[set $dimsperpagevar] > 500} {
                                set $maskvar 50
                            }
                        }
                    }
                }
            }
        }

        my db eval {
            select count(distinct pageid) as pagecnt from pages
        } break

        my postscript {
            %!PS-Adobe-3.0
            %%BoundingBox: $medium(llx) $medium(lly) $medium(urx) $medium(ury)
            %%Title: Yacop chart
            %%Creator: Yacop [package present yacop]
            %%CreationDate: [clock format [clock seconds] \
                                 -format "%Y-%m-%d %H:%M:%S"]
            %%Orientation: $Orientation
            %%Pages: $pagecnt
            %%DocumentMedia: $cfg(medium) $medium(width) $medium(height) 0 () ()
            %%DocumentNeededResources: font
            %%EndComments
            %%BeginProlog
        }

        set linewidth [expr {0.3/$ptsperdim}]
        set dotsize [expr {$linewidth*$cfg(dotsize)}]
        #set dotsize $cfg(dotsize)

        my postscript {
            /dt {
                newpath $dotsize 0 360 arc fill
            } def
        }

	foreach img [$chart dotimages] {
	    regexp {dot<([^>]*)>} $img -> e
	    foreach {r g b} [my Parsecol [$img cget -foreground]] break
	    my postscript {
                /sc$e { $r $g $b setrgbcolor } def
            }
	}

	foreach linfo [$chart linestyles] {
            dict with linfo {
                set line2num($name) [incr linecnt]
                set name $line2num($name)
                set width [expr {0.02*$width}]
                switch -- x$dash {
                    x {set dash "\[\] 0" }
                    x- {set dash "\[.1\] 0"}
                    x-. {set dash "\[.2\] 0"}
                    x-.. {set dash "\[.2 .4\] 0"}
                    default {
                        set y {}
                        foreach x $dash {
                            lappend y [expr {0.1*$x}]
                        }
                        set dash "\[$y\] 0"
                    }
                }
                my postscript {
                    /l$name {
                        lineto $dash setdash
                        $width setlinewidth stroke
                    } def
                }
            }
	}

        set fhgt [expr {$cfg(fontsize)/$ptsperdim}]

        my postscript {
            /pagewidth $medium(width)  def
            /pageheight $medium(height)  def
            /$cfg(font) findfont $fhgt scalefont setfont
            /writex { dup stringwidth pop 2 div neg -$fhgt rmoveto show } def
            /xwrite { dup stringwidth pop 2 div neg 0 rmoveto show } def
            /writey { dup stringwidth pop neg [expr {-$fhgt/2.0}] rmoveto show } def
            /ywrite { dup 0 [expr {-$fhgt/2.0}] rmoveto show } def
            %%EndProlog

            %%BeginSetup
            %%PaperSize: $cfg(medium)
            %%EndSetup
        }

        set pcnt 0

        my db eval {
            select pageid,minx,miny,maxx,maxy from pages order by rowid asc
        } {
            incr pcnt

            my postscript {
                %%Page: $minx-$maxx / $miny-$maxy
                %%BeginPageSetup
                gsave
            }

            set ominy $miny
            set omaxy $maxy
            set miny [expr {$miny * $y2x}]
            set maxy [expr {$maxy * $y2x}]

            if 0 {
                my postscript {
                    % code to mark the printable area (useful for debugging)
                    1 setlinewidth
                    $medium(llx) $medium(lly) moveto
                }
                foreach {x y} {
                    llx ury urx ury urx llx llx lly
                    urx ury llx ury urx lly
                } {
                    my postscript {
                        $medium($x) $medium($y) lineto \[\]
                        0 setdash stroke $medium($x) $medium($y) moveto
                    }
                }
            }

            my postscript {
                % shift to more convenient coordinates
                [expr {0.5*($medium(urx)+$medium(llx))}]
                [expr {0.5*($medium(ury)+$medium(lly))}] translate

                [expr {$portrait ? "" : "90 rotate"}]

                0.9 0.9 scale % margin

                $ptsperdim $ptsperdim scale
                [expr {-0.5*($minx+$maxx)}] [expr {-0.5*($miny+$maxy)}]
                translate

                %%EndPageSetup
            }

            # create axes

            foreach {x1 y1 x2 y2} {
                minx miny maxx miny
                minx maxy maxx maxy
                minx miny minx maxy
                maxx miny maxx maxy
            } {
                my postscript {
                    $linewidth setlinewidth
                    [set $x1] [set $y1] moveto
                    [set $x2] [set $y2] lineto
                    \[\] 0 setdash stroke
                }
            }

            set linewidthsmall [expr {$linewidth*0.8}]

            set ylines {}
            set xlines {}
            if {$cfg(showlines)} {
                set xcol 0.7
                lappend ylines [expr {$miny-.1*$fhgt}] [expr {$maxy+.1*$fhgt}]
                lappend xlines [expr {$minx-.7*$fhgt}] [expr {$maxx+.7*$fhgt}]
            } else {
                set xcol 0.2
                lappend ylines [expr {$miny-.2*$fhgt}] [expr {$miny+.2*$fhgt}]
                lappend ylines [expr {$maxy-.2*$fhgt}] [expr {$maxy+.2*$fhgt}]
                lappend xlines [expr {$minx-.2*$fhgt}] [expr {$minx+.2*$fhgt}]
                lappend xlines [expr {$maxx-.2*$fhgt}] [expr {$maxx+.2*$fhgt}]
            }

            set notthe1st false
            for {set x [expr {round($minx)}]} {$x <= $maxx} {incr x} {
                if {0 == ($x % $mskx)} {
                    my postscript {
                        0 setgray
                        $x [expr {$miny-.3*$fhgt}] moveto ($x) writex
                        $x [expr {$maxy+.5*$fhgt}] moveto ($x) xwrite
                    }
                }
                if {$notthe1st} {
                    foreach {y1 y2} $ylines {
                        my postscript {
                            [expr {$x-0.5}] $y1 moveto
                            [expr {$x-0.5}] $y2 lineto
                            $xcol setgray $linewidthsmall setlinewidth \[\] 0 setdash stroke
                        }
                    }
                }
                set notthe1st true
            }
            set notthe1st false
            for {set y [expr {round($ominy)}]} {$y <= $omaxy} {incr y} {
                if {0 == ($y % $msky)} {
                    my postscript {
                        0 setgray
                        [expr {$minx-.6*$fhgt}] [expr {$y2x*$y}] moveto
                        ($y ) writey
                        [expr {$maxx+.6*$fhgt}] [expr {$y2x*$y}] moveto
                        ($y) ywrite
                    }
                }
                if {$notthe1st} {
                    foreach {x1 x2} $xlines {
                        my postscript {
                            $x1 [expr {$y2x*($y-.5)}] moveto
                            $x2 [expr {$y2x*($y-.5)}] lineto
                            $xcol  setgray $linewidthsmall setlinewidth \[\] 0 setdash stroke
                        }
                    }
                }
                set notthe1st true
            }

            # create clipping path

            foreach {vname op} {minx - maxx + miny - maxy +} {
                set g$vname [expr [set $vname] $op (0.3*$fhgt)]
            }

            my postscript {
                gsave
                newpath
                $gminx $gminy moveto
                $gmaxx $gminy lineto
                $gmaxx $gmaxy lineto
                $gminx $gmaxy lineto
                closepath
                clip
                newpath
            }

            foreach {x y} {
                minx miny
                minx maxy
                maxx miny
                maxx maxy
            } {
                #append ps "[set $x] [set $y] moveto ($x,$y) show" \n
            }

            set cvs [$chart cvs]
            foreach id $cvsids($pageid) {
                switch -- [$cvs type $id] {
                    image {
                        $chart db eval {
                            select x,y * $y2x as y,filt as e from dots where cvsid=$id
                        } {
                            if {[string index $cfg(orient) 0] eq "h"} {
                                append output [format "%.3f %.3f sc%d dt\n" $y $x $e]
                            } else {
                                append output [format "%.3f %.3f sc%d dt\n" $x $y $e]
                            }
                        }
                    }
                    line {
                        $chart db eval {
                            select l.type as ltp,
                            s.x as sx, s.y * $y2x as sy, max(s.filt,t.filt) as e,
                            t.x as tx, t.y * $y2x  as ty
                            from lines as l
                            join dots as s on l.srcgen=s.genid
                            join dots as t on l.targen=t.genid
                            where l.cvsid = $id
                        } {
                            set tp $line2num($ltp)
                            if {[string index $cfg(orient) 0] eq "h"} {
                                append output [format "sc$e %.3f %.3f moveto %.3f %.3f l$tp\n" \
                                                   $sy $sx $ty $tx]
                            } else {
                                append output [format "sc$e %.3f %.3f moveto %.3f %.3f l$tp\n" \
                                                   $sx $sy $tx $ty]
                            }
                        }
                    }
                }
            }


            my postscript {
                grestore
                showpage
            }
        }

        my postscript {
            %%Trailer
            %%EOF
        }

        return $output
    }

}

# ------------------------------------------------

oo::class create PdfChart {

    variable db chart cfg medium cvsids mypdf page

    constructor {chcvs cfgdict} {

        set mypdf [namespace current]::pdf

	set chart $chcvs
        array set cfg $cfgdict

	yacop::sqlite [set db [namespace current]::chdb] :memory:

	my db eval {
            create table pages
            (pageid integer primary key,
             minx double, maxx double, miny double, maxy double);
            create index pageidx on pages(minx,maxx,miny,maxy);
	}

	foreach {w h} [pdf4tcl::getPaperSize $cfg(medium)] break

        switch -- [string index $cfg(orient) 0] {
            l {
                set ptsperdim [expr {$h/(1.0*$cfg(dpp))}]
                set spp [expr {int($w/($ptsperdim*$cfg(y2x)))}]
            }
            p {
                set ptsperdim [expr {$w/(1.0*$cfg(dpp))}]
                set spp [expr {int($h/($ptsperdim*$cfg(y2x)))}]
            }
        }

        if {$spp<1} {
            error "config has less than one homological degree per page"
        }

        set cfg(spp) $spp
        set cfg(ptsperdim) $ptsperdim

        # register pages

        for {set i 0} {$cfg(dimstart)+$i*$cfg(dpp) <= $cfg(dimstop)} {incr i} {
            for {set j 0} {$cfg(sdegstart)+$j*$cfg(spp) <= $cfg(sdegstop)} {incr j} {
                set minx [expr {$cfg(dimstart)+$i*$cfg(dpp)}]
                set maxx [expr {$cfg(dimstart)+(1+$i)*$cfg(dpp)}]
                set miny [expr {$cfg(sdegstart)+$j*$cfg(spp)}]
                set maxy [expr {$cfg(sdegstart)+(1+$j)*$cfg(spp)}]
                set ids [$chart find-overlapping \
                             [expr {$minx-1}] [expr {$miny-1}] \
                             [expr {$maxx+1}] [expr {$maxy+1}]]
                if {[llength $ids]} {
                    my db eval {
                        insert into pages(minx,maxx,miny,maxy)
                        values($minx,$maxx,$miny,$maxy)
                    }
                    set cvsids([my db last_insert_rowid]) $ids
                }
            }
        }
    }

    destructor {
        catch {$mypdf destroy}
    }

    method db {cmd args} {
	uplevel 1 [list $db $cmd] $args
    }

    method postscript {stuff} {
        return
    }

    method Parsecol {colspec} {
        if {[regexp -nocase -expanded {
            [\#]?([0-9a-f][0-9a-f])([0-9a-f][0-9a-f])([0-9a-f][0-9a-f])
        } $colspec total r g b]} {
            return [list [expr (0x$r)/255.0] [expr (0x$g)/255.0] [expr (0x$b)/255.0]]
        }
        error "color \"$colspec\" not understood"
    }

    method setcoords {minx maxx miny maxy} {
	set page(minx) $minx
	set page(miny) $miny
	set page(maxx) $maxx
	set page(maxy) $maxy

	set page(ysc) [expr {$page(height)/(1.0*$cfg(spp))}]
	set page(xsc) [expr {$page(ysc)/$cfg(y2x)}]
	set page(chxmin) [expr {-( ($page(maxx)-$page(minx))*$page(xsc) - $page(width)) / 2.0 }]
	set page(chymin) 0.0

	if {$page(chxmin)<0} {
	    # chart is too wide, rescale to fit width
	    set page(xsc) [expr {$page(width)/($page(maxx)-$page(minx))}]
	    set page(ysc) [expr {$page(xsc)*$cfg(y2x)}]
	    set page(chxmin) 0.0
	    set page(chymin) [expr {-(($page(maxy)-$page(miny))*$page(ysc) - $page(height)) / 2.0}]
	}

	set page(width) [expr {1.0*($maxx-$minx)}]
	set page(height) [expr {1.0*($maxy-$miny)}]
    }

    method Trafo {x y} {
	set xsc $cfg(ptsperdim)
	set ysc [expr {$xsc*$cfg(spp)}]
	list [expr {($x-$page(minx))*$page(xsc)+$page(chxmin)}] \
	    [expr {($y-$page(miny))*$page(ysc)+$page(chymin)}]
    }

    method line {x1 y1 x2 y2 args} {
	set a [my Trafo $x1 $y1]
	set b [my Trafo $x2 $y2]
	$mypdf line {*}$a {*}$b
    }

    method filtcolor {filt} {
	set var page(color-$filt)
	if {[info exists $var]} { return [set $var] }
	return {0 0 0}
    }

    method dot {x y filt} {
	$mypdf setLineDash 0
	$mypdf setStrokeColor {*}[my filtcolor $filt]
	$mypdf setFillColor {*}[my filtcolor $filt]
	$mypdf circle {*}[my Trafo $x $y] [expr {0.3*$cfg(dotsize)}] -filled 1
    }

    method setClippingPath {bdy} {
	# see section 8.5.4 in http://www.adobe.com/content/dam/Adobe/en/devnet/acrobat/pdfs/PDF32000_2008.pdf
	oo::objdefine $mypdf "export Pdfoutcmd Trans TransR"
	
	$mypdf Pdfoutcmd "q" ;# save graphics state

	foreach {w h} [$mypdf getDrawableArea] break

	set m 8
	set w [expr {$w+2*$m}]
	set h [expr {$h+2*$m}]
	
	$mypdf Trans -$m -$m x y
	$mypdf TransR $w $h w h
	
	$mypdf Pdfoutcmd $x $y $w $h re
	$mypdf Pdfoutcmd "W" ;# set clipping path
	$mypdf Pdfoutcmd "n" 
	set rc [catch {uplevel 1 $bdy} errmsg options]
	$mypdf Pdfoutcmd "Q" ;# restore graphics state
	return -options $options $errmsg
    }
    
    method getchart {} {

        set portrait true
        set Orientation Portrait
        if {[string match l* $cfg(orient)]} {
            set Orientation Landscape
            set portrait false
        }

        foreach key {dpp spp ptsperdim y2x} {
            set $key $cfg($key)
        }

        # determine how to label the axes
        foreach {maskvar dimsperpagevar} {
            mskx dpp msky spp
        } {
            set $maskvar 1
            if {[set $dimsperpagevar] > 5} {
                set $maskvar 2
                if {[set $dimsperpagevar] > 15} {
                    set $maskvar 5
                    if {[set $dimsperpagevar] > 25} {
                        set $maskvar 10
                        if {[set $dimsperpagevar] > 100} {
                            set $maskvar 20
                            if {[set $dimsperpagevar] > 500} {
                                set $maskvar 50
                            }
                        }
                    }
                }
            }
        }

        my db eval {
            select count(distinct pageid) as pagecnt from pages
        } break

        pdf4tcl::new $mypdf -paper $cfg(medium) -margin 24 -orient 0 -unit p

        $mypdf metadata -title "Yacop chart" -creator "Yacop [package present yacop]" \
	    -creationdate [clock seconds]

        $mypdf setFont 10 Helvetica

        set linewidth 2
        set dotsize [expr {$linewidth*$cfg(dotsize)}]
        #set dotsize $cfg(dotsize)

        my postscript {
            /dt {
                newpath $dotsize 0 360 arc fill
            } def
        }

	foreach img [$chart dotimages] {
	    regexp {dot<([^>]*)>} $img -> e
	    foreach {r g b} [my Parsecol [$img cget -foreground]] break
	    set page(color-$e) [list $r $g $b]
	}

	foreach linfo [$chart linestyles] {
            dict with linfo {
                set line2num($name) [incr linecnt]
                set width [expr {0.9*$width}]
                switch -- x$dash {
                    x {set dash "" }
                    x- {set dash "3 3"}
                    x-. {set dash "6 6"}
                    x-.. {set dash "6 9"}
                    default {
                        set y {}
                        foreach x $dash {
                            lappend y [expr {2.1*$x}]
                        }
                        set dash "$y 0"
                    }
                }
		set linestyle($name) [list $width {*}$dash]
            }
	}

	$mypdf setFont $cfg(fontsize) Times-Roman

        set pcnt 0

        my db eval {
            select pageid,minx,miny,maxx,maxy from pages order by rowid asc
        } {
            incr pcnt

            $mypdf startPage -landscape [regexp -nocase landscape $Orientation]

            set ominy $miny
            set omaxy $maxy
            set miny [expr {$miny * $y2x}]
            set maxy [expr {$maxy * $y2x}]

	    foreach {page(width) page(height)} [$mypdf getDrawableArea] break


            if 0 {

		# code to mark the printable area (useful for debugging)
                foreach {width height} [$mypdf getDrawableArea] break
		$mypdf setLineStyle 0.5 8 4
		$mypdf setStrokeColor 0.8 0 0
		$mypdf setFillColor 0.6 0.9 0.4
		$mypdf rectangle 0 0 $width $height -filled 1

		foreach x [list 0 [expr {$width/2.0}] $width] {
		    foreach y [list 0 [expr {$height/2.0}] $height] {
			$mypdf text "($x,$y)" -align center -x $x -y $y
		    }
		}
	    }

	    my setcoords $minx $maxx $miny $maxy

	    $mypdf setStrokeColor 0 0 0
	    $mypdf setFillColor 0 0 0

            # create axes

	    $mypdf setLineDash 0
            foreach {x1 y1 x2 y2} {
                minx miny maxx miny
                minx maxy maxx maxy
                minx miny minx maxy
                maxx miny maxx maxy
            } {
		my line [set $x1] [set $y1] [set $x2] [set $y2]
            }

            set linewidthsmall [expr {$linewidth*0.8}]
	    set fhgt 1

            set ylines {}
            set xlines {}
            if {$cfg(showlines)} {
                set xcol 0.7
                lappend ylines [expr {$miny-.1*$fhgt}] [expr {$maxy+.1*$fhgt}]
                lappend xlines [expr {$minx-.7*$fhgt}] [expr {$maxx+.7*$fhgt}]
            } else {
                set xcol 0.2
                lappend ylines [expr {$miny-.2*$fhgt}] [expr {$miny+.2*$fhgt}]
                lappend ylines [expr {$maxy-.2*$fhgt}] [expr {$maxy+.2*$fhgt}]
                lappend xlines [expr {$minx-.2*$fhgt}] [expr {$minx+.2*$fhgt}]
                lappend xlines [expr {$maxx-.2*$fhgt}] [expr {$maxx+.2*$fhgt}]
            }

	    $mypdf setLineWidth  $linewidthsmall

            set notthe1st false
            for {set x [expr {round($minx)}]} {$x <= $maxx} {incr x} {
                if {0 == ($x % $mskx)} {
		    $mypdf setTextPosition {*}[my Trafo $x $miny]
		    $mypdf moveTextPosition 0 -$cfg(fontsize)
		    $mypdf text $x -align center
		    $mypdf setTextPosition {*}[my Trafo $x $maxy]
		    $mypdf moveTextPosition 0 [expr {0.3*$cfg(fontsize)}]
		    $mypdf text $x -align center
                }
                if {$notthe1st} {
                    foreach {y1 y2} $ylines {
			my line [expr {$x-0.5}] $y1 [expr {$x-0.5}] $y2
                    }
                }
                set notthe1st true
            }
	    set offsety [expr {-$cfg(fontsize)/2.0}]
            set notthe1st false
            for {set y [expr {round($ominy)}]} {$y <= $omaxy} {incr y} {
                if {0 == ($y % $msky)} {
		    $mypdf setTextPosition {*}[my Trafo $minx $y]
		    $mypdf moveTextPosition -3 $offsety
		    $mypdf text $y -align right
		    $mypdf setTextPosition {*}[my Trafo $maxx $y]
		    $mypdf moveTextPosition 3 $offsety
		    $mypdf text $y -align left
                }
                if {$notthe1st} {
                    foreach {x1 x2} $xlines {
			my line $x1 [expr {$y2x*($y-.5)}] $x2 [expr {$y2x*($y-.5)}]
                    }
                }
                set notthe1st true
            }

	    my setClippingPath {
		set cvs [$chart cvs]
		foreach id $cvsids($pageid) {
		    switch -- [$cvs type $id] {
			image {
			    $chart db eval {
				select x,y * $y2x as y,filt as e from dots where cvsid=$id
			    } {
				my dot $x $y $e
			    }
			}
			line {
			    $chart db eval {
				select l.type as ltp,
				s.x as sx, s.y * $y2x as sy, max(s.filt,t.filt) as e,
				t.x as tx, t.y * $y2x  as ty
				from lines as l
				join dots as s on l.srcgen=s.genid
				join dots as t on l.targen=t.genid
				where l.cvsid = $id
			    } {
				$mypdf setStrokeColor {*}[my filtcolor $e]
				$mypdf setFillColor {*}[my filtcolor $e]
				set tp $line2num($ltp)
				$mypdf setLineStyle {*}$linestyle($ltp)
				my line $sx $sy $tx $ty
			    }
			}
		    }
		}
	    }

        }

        set res [$mypdf get]
        $mypdf destroy
        return $res
    }

}

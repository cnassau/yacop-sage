r"""
Tcl interface for the Yacop package.

AUTHORS: - Christian Nassau (2009-03-27: version 1.0)

CLASS DOCUMENTATION:
"""

from tkinter import Tcl, Tk, TclError
from sage.misc.cachefunc import cached_method
from sage.misc.lazy_attribute import lazy_attribute
import os

# *****************************************************************************
#       Copyright (C) 2009-2011 Christian Nassau <nassau@nullhomotopie.de>
#  Distributed under the terms of the GNU General Public License (GPL)
# *****************************************************************************


def tcl_interp():
    """
    create a new Tcl interpreter with the standard packages loaded

    TESTS::

        sage: from yacop.utils.tcl import tcl_interp, tcl_eval
        sage: tcl = tcl_interp()
        sage: tcl.eval("package present sqlite3") # random
        3.8.2
    """
    tcl = Tcl()
    xdirs = Yacop.tcllibrary
    if not xdirs is None:
        if not isinstance(xdirs, list):
            xdirs = [xdirs]
            [tcl.eval("lappend auto_path {%s}" % path) for path in xdirs]
    tcl.eval(
        """
        lappend auto_path $::env(SAGE_LOCAL)/tcl/lib
        lappend auto_path $::env(SAGE_LOCAL)/lib
        package require yacop::sage 1.0
            """
    )
    return tcl


def tcl_eval(tcl, script):
    """
    Execute a Tcl script, with error reporting.

    EXAMPLE::

        sage: from yacop.utils.tcl import tcl_interp, tcl_eval
        sage: tcl_eval(tcl_interp(),"oops")
        Traceback (most recent call last):
        ...
        TclError: invalid command name "oops"
            while executing
        "oops"

    """
    try:
        return tcl.eval(script)
    except TclError as e:
        einf = tcl.eval("set ::errorInfo")
        raise TclError(einf)


def loadTk(tcl):
    "Load the Tk widget library into a interpreter"

    tcl_eval(
        tcl,
        """
       namespace eval :: {package require Tk}
       if {![winfo exists .yacop]} {
           set x {}
           lappend x "I am the Yacop main window."
           lappend x "You should not see me."
           lappend x "If you close me, Yacop GUIs will no longer work."
           label .yacop -text [join $x \\n]
           pack .yacop -expand 1 -fill both
           wm title . "Yacop main window"

           set ::yacop::LastUpdate [clock milliseconds]
           proc ::yacop::progress {} {
                variable LastUpdate
                set now [clock milliseconds]
                if {$now-$LastUpdate > 300} {
                   set LastUpdate $now
                   update
                }
           }
       }
       wm withdraw .
     """,
    )


class Yacop:
    """
    Interface to yet another cohomology program (YaCoP).
    """

    class defaults:
        memdb = False
        datadir = None

    @staticmethod
    def data_dir():
        import os

        ans = Yacop._data_dir()
        if not os.path.isdir(ans):
            os.makedirs(ans)
        return ans

    @staticmethod
    def _data_dir():
        if not Yacop.defaults.datadir is None:
            return Yacop.defaults.datadir

        if "YACOP_DATA" in os.environ:
            return os.environ["YACOP_DATA"]

        dname = "yacop_data"

        if "YACOP_DATA" in os.environ:
            return os.path.join(os.environ["YACOP_DATA"], dname)

        if "HOME" in os.environ:
            return os.path.join(os.environ["HOME"], dname)

        return os.path.join(os.environ["SAGE_ROOT"], dname)

    tcl = None
    "The main Tcl interpreter. Resolutions use a namespace of this as their interpreter."

    tcllibrary = None
    "Extra paths, added to auto_path when Tcl starts up"

    def __init__(self):
        pass

    def loadTkOnce(self):
        loadTk(self.main)

    class Interpreter:
        "A namespace in the main Yacop interpreter"

        def __init__(self):
            self._namespace = Yacop.main.eval("yacop::sage::new-namespace")

        def __del__(self):
            if not self._namespace is None:
                Yacop.main.eval("catch {namespace delete %s}" % self._namespace)

        def eval(self, script):
            "Execute a Tcl script in the Interpreter's namespace"
            return tcl_eval(
                Yacop.main, "namespace eval {%s} {%s}" % (self._namespace, script)
            )

        def loadTk(self):
            Yacop.loadTkOnce()

        def createcommand(self, name, callback):
            Yacop.main.createcommand("%s::%s" % (self._namespace, name), callback)

        class Coroutine(object):
            def __init__(self, tcl, cmdname):
                self.tcl = tcl
                self._cmd = cmdname
                global coroutine_cnt
                coroutine_cnt += 1
                self._cor = "yacop_coroutine%d" % coroutine_cnt

            def __enter__(self):
                self.tcl.eval("coroutine %s %s" % (self._cor, self._cmd))
                return self

            def __exit__(self, *excargs):
                self.tcl.eval("catch {rename %s {}}" % self._cor)
                return False

            def __iter__(self):
                return self

            def __next__(self):
                x = self.tcl.eval(self._cor)
                if len(x) == 0:
                    raise StopIteration
                return x

        def coroutine(self, cmdname):
            return Yacop.Interpreter.Coroutine(self, cmdname)


coroutine_cnt = 0

Yacop.main = tcl_interp()

# Local Variables:
# eval:(add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
# End:

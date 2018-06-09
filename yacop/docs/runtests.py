"""

    TESTS::

        sage: import yacop.docs.runtests
        sage: yacop.docs.runtests.Run()
        Executing notebooks in directory yacop/docs/jupyter
        ...
        ok
        sage: yacop.docs.runtests.numtests > 0
        True
"""

import sys, os
import filecmp
from fnmatch import fnmatch
import warnings
warnings.filterwarnings("ignore",category=DeprecationWarning)
import nbformat
from nbconvert import HTMLExporter, RSTExporter, MarkdownExporter
from nbconvert.preprocessors import ExecutePreprocessor

class Tester(object):
    
    def __init__(self,path,name):
        fname = os.path.join(path, name)
        with open(fname, "r") as f: 
            self.json = f.read()
            self.nb = nbformat.reads(self.json, as_version=4)
            basename = os.path.splitext(name)[0]
            self.outfname = os.path.join(path,'ref',basename + ".new")
            self.refname  = os.path.join(path,'ref',basename + ".md")
        self.exp = RSTExporter()
        #self.exp.template_file = 'basic'
    
    def runtest(self):
        warnings.filterwarnings("ignore",category=DeprecationWarning)
        ep = ExecutePreprocessor(timeout=600, kernel_name='sagemath',allow_errors=True)
        ep.preprocess(self.nb, {})
        (body, resources) = self.exp.from_notebook_node(self.nb)
        with open(self.outfname,'wt') as f:
            f.write(body)
        if not filecmp.cmp(self.outfname,self.refname):
            raise ValueError, "files %s and %s differ" % (self.outfname,self.refname)
        

numtests = 0
    
def Run():
    global numtests
    root = 'yacop/docs/jupyter'
    pattern = "*.ipynb"
    errs = []
    print("Executing notebooks in directory", root)
    for path, subdirs, files in os.walk(root):
        for name in files:
            if fnmatch(name, pattern):
                numtests = numtests + 1
                print("   ", name)
                try:
                    Tester(path, name).runtest()
                except Exception as e:
                    print("     ", e)
                    errs.append(name)
    if len(errs)>0:
        print("errors: ", ", ".join(errs))
    else:
        print("ok")

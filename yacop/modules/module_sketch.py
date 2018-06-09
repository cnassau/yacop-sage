from sage.structure.sage_object import SageObject

class gen(SageObject):
    def __init__(self,x):
        self.data = x
    def _repr_(self):
        return "((%s))" % self.data

class ModuleSketch(SageObject):
     def __init__(self):
         self.g = gen

gen = ModuleSketch.gen

class mymodule(ModuleSketch):

    def generators():
        x = g(17)

        y = Sq(8)*x

S=mymodule()



r"""
Doctests for testing the handling of the internal differential
"""

#pylint: disable=E0213

"""
TESTS::

sage: from yacop.modules.serre_cartan import SerreCartanModule
sage: basis = [("a%d"%deg,deg,0,0) for deg in (1,)]
sage: basis += [("b%d"%deg,deg,0,1) for deg in (1,2,3)]
sage: basis += [("c%d"%deg,deg,0,2) for deg in (2,3,4,5)]
sage: basis += [("d%d"%deg,deg,0,3) for deg in (4,5)]
sage: M=SerreCartanModule(SteenrodAlgebra(2),basis)
sage: M
Free module generated by [a1, b1, b2, b3, c2, c3, c4, c5, d4, d5] over Finite Field of size 2
sage: for s in (0,1,2,3,4):
....:      print (s,sorted(M.graded_basis(s=s)))
0 [a1]
1 [b1, b2, b3]
2 [c2, c3, c4, c5]
3 [d4, d5]
4 []
sage: M.inject_variables()
Defining a1, b1, b2, b3, c2, c3, c4, c5, d4, d5
sage: M.set_operations([(Sq(1),b1,b2),(Sq(2),c2,c4),(Sq(1),c3,c4),(Sq(2),c3,c5)])
sage: for g in sorted(M.gens()):
....:     print(g,[(Sq(i),g,Sq(i)*g) for i in range(1,10) if not (Sq(i)*g).is_zero()])
a1 []
b1 [(Sq(1), b1, b2)]
b2 []
b3 []
c2 [(Sq(2), c2, c4)]
c3 [(Sq(1), c3, c4), (Sq(2), c3, c5)]
c4 []
c5 []
d4 []
d5 []
sage: [(g,g.differential()) for g in sorted(M.gens()) if not g.differential().is_zero()]
[]
sage: M.differential_set([(b1,a1),(c2,b2),(c3,b3),(d4,c4),(d5,c5)])
sage: [(g,g.differential()) for g in sorted(M.gens()) if not g.differential().is_zero()]
[(b1, a1), (c2, b2), (c3, b3), (d4, c4), (d5, c5)]

sage: N=cartesian_product((M,M))
sage: for n in sorted(N.graded_basis()):
....:     if not n.differential().is_zero():
....:         print(n,n.differential())
(b1, 0) (a1, 0)
(c2, 0) (b2, 0)
(c3, 0) (b3, 0)
(d4, 0) (c4, 0)
(d5, 0) (c5, 0)
(0, b1) (0, a1)
(0, c2) (0, b2)
(0, c3) (0, b3)
(0, d4) (0, c4)
(0, d5) (0, c5)
sage: N.differential_clear()
sage: [n for n in sorted(N.graded_basis()) if not n.differential().is_zero()]
[]
sage: N.differential_set([(N.summand_embedding(0)(b1),N.summand_embedding(1)(a1))])
sage: for n in sorted(N.graded_basis()):
....:     if not n.differential().is_zero():
....:         print(n,n.differential())
(b1, 0) (0, a1)
sage: N.differential_reset()
sage: for n in sorted(N.graded_basis()):
....:     if not n.differential().is_zero():
....:         print(n,n.differential())
(b1, 0) (a1, 0)
(c2, 0) (b2, 0)
(c3, 0) (b3, 0)
(d4, 0) (c4, 0)
(d5, 0) (c5, 0)
(0, b1) (0, a1)
(0, c2) (0, b2)
(0, c3) (0, b3)
(0, d4) (0, c4)
(0, d5) (0, c5)

sage: X=SerreCartanModule(SteenrodAlgebra(2),(("x",0,0,1),("y",0,0,0)))
sage: X.inject_variables()
Defining x, y
sage: X.differential_set([(x,y)])
sage: T=tensor((X,M))
sage: for n in sorted(T.graded_basis()):
....:     if not n.differential().is_zero():
....:         print(n,"->",n.differential())
x # a1 -> y # a1
x # b1 -> x # a1 + y # b1
x # b2 -> y # b2
x # b3 -> y # b3
x # c2 -> x # b2 + y # c2
x # c3 -> x # b3 + y # c3
x # c4 -> y # c4
x # c5 -> y # c5
x # d4 -> x # c4 + y # d4
x # d5 -> x # c5 + y # d5
y # b1 -> y # a1
y # c2 -> y # b2
y # c3 -> y # b3
y # d4 -> y # c4
y # d5 -> y # c5

"""

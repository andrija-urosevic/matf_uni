from z3 import *

# Dve nemimoilazne prave se seku ili su paralelene.
# Prave koje se seku leže u istoj ravni.
# Prave koje su paralelene leže u istoj ravni.
# Dve nemimoilazne prave leže u istoj ravni.

B = BoolSort()
P = DeclareSort('Prava')

m = Function('m', P, P, B)
s = Function('s', P, P, B)
p = Function('p', P, P, B)
r = Function('r', P, P, B)

x, y = Consts('x y', P)

axioms = [
    ForAll([x, y], Implies(Not(m(x, y)), Or(s(x, y), p(x, y)))),
    ForAll([x, y], Implies(s(x, y), r(x, y))),
    ForAll([x, y], Implies(p(x, y), r(x, y)))
]

theorem = ForAll([x, y], Implies(Not(m(x, y)), r(x, y)))

s = Solver()
s.add(theorem)

print(s.check(axioms))




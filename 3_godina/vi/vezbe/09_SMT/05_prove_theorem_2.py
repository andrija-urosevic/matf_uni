from z3 import *

# Svaka dva brata imaju zajedničkog roditelja.
# Roditelj je stariji od deteta.
# Postoje braća.
# Ni jedna osoba nije starija od druge.

P = DeclareSort('Person')
B = BoolSort()

b = Function('b', P, P, B)
r = Function('r', P, P, B)
s = Function('s', P, P, B)

x, y, z = Consts('x y z', P)

axioms = [
    ForAll([x, y], Exists([z], Implies(b(x, y), And(r(z, x), r(z, y))))),
    ForAll([x, y], Implies(r(x, y), s(x, y))),
    Exists([x, y], b(x, y))
]

theorem = ForAll([x, y], Not(s(x, y)))

s = Solver()
s.add(theorem)

print(s.check(axioms))




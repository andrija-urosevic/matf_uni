from z3 import *

B = BoolSort()
Z = IntSort()

f = Function('f', B, Z)
g = Function('f', Z, B)

a = Bool('a')

solve(g(1 + f(a)))

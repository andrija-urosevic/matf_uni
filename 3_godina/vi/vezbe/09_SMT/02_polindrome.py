from z3 import *

A, B, C, D = Bools('A B C D')

s = Solver()

s.add(A == D)
s.add(B == C)
s.add(Not(A == B))

print(s.check())
print(s.model())


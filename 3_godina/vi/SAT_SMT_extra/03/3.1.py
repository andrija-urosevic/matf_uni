from z3 import *

s = Solver()

x, y, z = Ints('x y z')
s.add(x == 3)
s.add(y == 2)
s.add(z == x + y)

print(s.check())
print(s.model())

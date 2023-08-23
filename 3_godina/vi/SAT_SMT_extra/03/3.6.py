from z3 import *

x, y = Reals('x y')

s = Solver()

s.add(x > 0)
s.add(y > 0)

s.add(x + y == 4*x*y)

print(s.check())
if s.check() == sat:
    m = s.model()
    print(m)
    print(m.evaluate(1/x + 1/y))

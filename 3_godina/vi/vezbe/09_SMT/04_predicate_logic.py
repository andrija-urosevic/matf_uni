from z3 import *

x, y = Ints('x y')

solve([x == y + 1, ForAll([y], Implies(y <= 0, x <= y))])

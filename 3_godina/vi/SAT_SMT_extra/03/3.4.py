from z3 import *

s = Solver()

rabbit, cat, dog = Ints('rabbit cat dog')

s.add(rabbit > 0)
s.add(cat > 0)
s.add(dog > 0)

s.add(rabbit + cat  == 10)
s.add(rabbit + dog  == 20)
s.add(dog + cat     == 24)

if s.check() == sat:
    m = s.model()
    print(m)
    print(m[rabbit].as_long() + m[cat].as_long() + m[dog].as_long())


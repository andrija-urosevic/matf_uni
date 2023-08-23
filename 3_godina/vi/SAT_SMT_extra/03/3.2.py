from z3 import *

s = Solver()
a, b, c, d, e, f = Ints('a b c d e f')
s.add(215*a + 275*b + 335*c + 355*d + 420*e + 580*f == 1505)
s.add(a >= 0, b >= 0, c >= 0, d >= 0, e >= 0, f >= 0)

while s.check() == sat:
    m = s.model()
    print(m)
    s.add(Not(And(a == m[a], b == m[b], c == m[c],
                  d == m[d], e == m[e], f == m[f])))


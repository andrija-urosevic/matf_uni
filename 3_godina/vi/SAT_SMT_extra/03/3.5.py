from z3 import *

set = [-7, -3, -2, 5, 8]
n = len(set)

vars = [Int('vars[%d]' % i) for i in range(n)]

s = Solver()

bool_list = []

for i in range(n):
    bool_list.append(vars[i] * set[i])
    s.add(Or(vars[i] == 0, vars[i] == 1))

s.add(sum(bool_list) == 0)
s.add(sum(vars) >= 1)

print(s.check())
if s.check() == sat:
    m = s.model()
    for i in range(n):
        if m[vars[i]].as_long() == 1:
            print(set[i], end=" ")


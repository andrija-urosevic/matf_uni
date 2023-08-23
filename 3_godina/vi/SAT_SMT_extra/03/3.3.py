from z3 import *

s = Optimize()

total_workpieces = Int('total_workpieces')
cut_A, cut_B, cut_C, cut_D = Ints('cut_A cut_B cut_C cut_D')
out_A, out_B = Ints('out_A out_B')

s.add(total_workpieces == cut_A + cut_B + cut_C + cut_D)

s.add(cut_A >= 0)
s.add(cut_B >= 0)
s.add(cut_C >= 0)
s.add(cut_D >= 0)

s.add(out_A == 3*cut_A + 2*cut_B + 1*cut_C + 0*cut_D)
s.add(out_B == 1*cut_A + 6*cut_B + 9*cut_C + 13*cut_D)

s.add(out_A == 800)
s.add(out_B == 400)

s.minimize(total_workpieces)

print(s.check())
print(s.model())


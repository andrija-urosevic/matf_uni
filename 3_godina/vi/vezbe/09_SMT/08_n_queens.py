from z3 import *

n = 8

Q = [ Int(f'Q_{i+1}') for i in range(n) ]

val_c = [ And(1 <= Q[i], Q[i] <= 8) for i in range(n) ]

col_c = [ Distinct(Q) ]

diag_c = [
    And(Q[i] - Q[j] != i - j, Q[i] - Q[j] != j - i) if i != j else True
    for i in range(n) for j in range(n)
]

result = solve(val_c + col_c + diag_c)



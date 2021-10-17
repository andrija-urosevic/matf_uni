from z3 import *

X = [[Int(f'X_{i+1}{j+1}') for j in range(9)] for i in range(9)]

cells_c = [And(1 <= X[i][j], X[i][j] <= 9) for j in range(9) for i in range(9)]

rows_c = [Distinct(X[i]) for i in range(9)]

cols_c = [Distinct([X[i][j] for i in range(9)]) for j in range(9)]

sq_c = [Distinct([X[3*i0 + i][3*j0 + j]
                  for i in range(3) for j in range(3)])
        for i0 in range(3) for j0 in range(3)]

sudoku_c = cells_c + rows_c + cols_c + sq_c

instance = [[0,0,0,0,9,4,0,3,0],
            [0,0,0,5,1,0,0,0,7],
            [0,8,9,0,0,0,0,4,0],
            [0,0,0,0,0,0,2,0,8],
            [0,6,0,2,0,1,0,5,0],
            [1,0,2,0,0,0,0,0,0],
            [0,7,0,0,0,0,5,2,0],
            [9,0,0,0,6,5,0,0,0],
            [0,4,0,9,7,0,0,0,0]]

instance_c = [X[i][j] == instance[i][j] if instance[i][j] != 0 else True
              for i in range(9) for j in range(9)]

s = Solver()
s.add(sudoku_c + instance_c)

if s.check() == sat:
    print(s.model())


import json
import constraint

filename = input('Unesite ime fajla:\n')

with open(filename, 'r') as f:
    sudoku = json.load(f)
    print(sudoku)

problem = constraint.Problem()

for i in range(9):
    problem.addVariables(range(i*10 + 1, i*10 + 10), range(1,10))

for i in range(9):
    problem.addConstraint(
            constraint.AllDifferentConstraint(),
            range(i*10 + 1, i*10 + 10)
    )

for i in range(9):
    problem.addConstraint(
            constraint.AllDifferentConstraint(),
            range(0 + i, 90 + i, 10)
    )

for i in [0, 3, 6]:
    for j in [0, 3, 6]:
        positions = [10*i + j, 10*i + j + 1, 10*i + j + 2,
                     10*(i+1) + j, 10*(i+1) + j + 1, 10*(i+1) + j + 2,
                     10*(i+2) + j, 10*(i+2) + j + 1, 10*(i+2) + j + 2]
        problem.addConstraint(
                constraint.AllDifferentConstraint(),
                positions
        )

for i in range(9):
    for j in range(9):
        if sudoku[i][j] != 0:
            def sudoku_constraint(value, sudoku_value=sudoku[i][j]):
                return value == sudoku_value
            problem.addConstraint(sudoku_constraint, [10*i+j])



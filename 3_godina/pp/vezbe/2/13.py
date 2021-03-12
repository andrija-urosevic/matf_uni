import constraint

problem = constraint.Problem()

problem.addVariables('12345678', range(1,9))

problem.addConstraint(constraint.AllDifferentConstraint())

for i in '12345678':
    for j in '12345678':
        if int(i) < int(j):
            def diagonal_constraint(x, y, _x=i, _y=j):
                return abs(x-y) != int(_y) - int(_x)
            problem.addConstraint(diagonal_constraint, [i, j])

solutions = problem.getSolutions()
num_solutions = len(solutions)
for r in solutions:
    print('----------------')
    for i in '12345678':
        for j in range(1,9):
            if r[i] == j:
                print('D', end=' ')
            else:
                print(' ', end=' ')
        print()
    print('----------------')
print(f'Broj resenja je {num_solutions:d}')

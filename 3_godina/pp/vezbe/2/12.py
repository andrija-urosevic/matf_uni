import constraint

problem = constraint.Problem()

problem.addVariables('12345678', range(1,9))

problem.addConstraint(constraint.AllDifferentConstraint())

for r in problem.getSolutions():
    print('----------------')
    for i in '12345678':
        for j in range(1,9):
            if r[i] == j:
                print('T', end=' ')
            else:
                print(' ', end=' ')
        print()
    print('----------------')

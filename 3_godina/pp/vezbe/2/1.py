import constraint

problem = constraint.Problem()

problem.addVariable('x', ['a', 'b', 'c'])
problem.addVariable('y', [1, 2, 3])
problem.addVariable('z', [0.1, 0.2, 0.3])

problem.addConstraint(lambda y, z: y / 10 == z, ['y', 'z'])

for solution in problem.getSolutions():
    print(solution)

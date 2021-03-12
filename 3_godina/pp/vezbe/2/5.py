import constraint

problem = constraint.Problem()

problem.addVariable('x', range(1, 91))
problem.addVariable('y', range(2, 61, 2))
problem.addVariable('z', [i**2 for i in range(1, 11)])

problem.addConstraint(
        lambda x, y, z: x >= z and 2*x + x*y + z <= 34,
        ['x', 'y', 'z']
)

for solution in problem.getSolutions():
    print(solution)

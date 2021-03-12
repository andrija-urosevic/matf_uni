import constraint

problem = constraint.Problem()

problem.addVariable('X', range(1,11))
problem.addVariable('Y', range(1,52,2))
problem.addVariable('Z', [i*10 for i in range(1,11)])
problem.addVariable('W', [i**3 for i in range(1,11)])

problem.addConstraint(
        lambda x, y, z, w: x >= 2*w and 3 + y <= z and x - 11*w + y + 10*z <= 100,
        ['X', 'Y', 'Z', 'W']
)

for solution in problem.getSolutions():
    print(solution)


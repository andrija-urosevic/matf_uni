import constraint

problem = constraint.Problem()

problem.addVariable('1din', range(51))
problem.addVariable('2din', range(26))
problem.addVariable('5din', range(11))
problem.addVariable('10din', range(6))
problem.addVariable('20din', range(4))

# problem.addConstraint(lambda x, y, z, u, v: x + 2*y + 5*z + 10*u + 20*v == 50, ['1din', '2din', '5din', '10din', '20din'])
problem.addConstraint(
        constraint.ExactSumConstraint(50, [1, 2, 5, 10, 20]),
        ['1din', '2din', '5din', '10din', '20din']
)

for solution in problem.getSolutions():
    print(solution)

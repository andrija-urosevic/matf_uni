import constraint

problem = constraint.Problem()

problem.addVariables('TF', range(1, 10))
problem.addVariables('WOUR', range(10))

problem.addConstraint(constraint.AllDifferentConstraint())
problem.addConstraint(
        lambda t, f, w, o, u, r: 2*(100*t + 10*w + o) == 1000*f + 100*o + 10*u + r,
        'TFWOUR'
)

for solution in problem.getSolutions():
    print(solution)

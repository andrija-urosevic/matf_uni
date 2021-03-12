import constraint

problem = constraint.Problem()

problem.addVariable('A', range(1,10))
problem.addVariable('B', range(10))
problem.addVariable('C', range(10))

problem.addConstraint(constraint.AllDifferentConstraint())

min_value = 999
min_solution = {}
for solution in problem.getSolutions():
    curr_value = 100 * solution['A'] + 10 * solution['B'] + solution['C'] / (solution['A'] + solution['B'] + solution['C'])
    if min_value > curr_value:
        min_value = curr_value
        min_solution = solution


print(min_solution)

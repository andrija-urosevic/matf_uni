import constraint

# 10e = 1170din

problem = constraint.Problem()

problem.addVariable("#brasno", range(0, 11))
problem.addVariable("#plazma", range(0, 21))
problem.addVariable("#jaja", range(0, 8))
problem.addVariable("#mleko", range(0, 6))
problem.addVariable("#visnja", range(0, 4))
problem.addVariable("#nutela", range(0, 9))

problem.addConstraint(
        constraint.ExactSumConstraint(10)
)
problem.addConstraint(
        constraint.MaxSumConstraint(1170, [30, 300, 50, 170, 400, 450])
)
problem.addConstraint(
        constraint.MaxSumConstraint(500, [30, 10, 150, 32, 3, 15])
)
problem.addConstraint(
        constraint.MaxSumConstraint(150, [5, 30, 2, 15, 45, 68])
)

best_protein = -1
for solution in problem.getSolutions():
    kolicina_proteina = 20 * solution["#brasno"]\
                      + 15 * solution["#plazma"]\
                      + 70 * solution["#jaja"]\
                      + 40 * solution["#mleko"]\
                      + 40 * solution["#visnja"]\
                      + 7 * solution["#nutela"]
    if best_protein < kolicina_proteina:
        best_protein = kolicina_proteina

print(best_protein)

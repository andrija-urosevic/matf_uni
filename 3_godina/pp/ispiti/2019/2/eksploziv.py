import constraint

# prenose eksploziv
# 20kg=20000g nosivost
# 50dm3=50000cm3 zapremina
# 17000din budzet
# max razarna moc

problem = constraint.Problem()

problem.addVariable("#M-84", range(0, 5))
problem.addVariable("#M-75", range(0, 31))
problem.addVariable("#P98", range(0, 11))
problem.addVariable("#TMA-4", range(0, 21))
problem.addVariable("#TMPR-6", range(0, 6))

problem.addConstraint(
        constraint.MaxSumConstraint(20000, [480, 355, 160, 30, 72])
)
problem.addConstraint(
        constraint.MaxSumConstraint(17000, [1000, 2500, 800, 7000, 10000])
)
problem.addConstraint(
        constraint.MaxSumConstraint(50000, [6*11.5, 5.7*8.9, 2*2, 28.5*110, 29*132])
)

energy = -1
for solution in problem.getSolutions():
    power = 5.6  * solution["#M-84"]\
          + 9.9  * solution["#M-75"]\
          + 2.7  * solution["#P98"]\
          + 30.5 * solution["#TMA-4"]\
          + 45.4 * solution["#TMPR-6"]

    energy = max(energy, power)

print(energy)




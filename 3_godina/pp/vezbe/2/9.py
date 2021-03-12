import constraint

# 1xhleb <- 10min
# 2xkifla <- 12min

# 1xhleb <- 300g brasno
# 1xkifla <- 120g brasno

# 1xhelb -> 7din
# 1xkifla -> 9din

# 20h = 20*60min = 1200min
# 20kg = 20000g brasno

# zarada = #hleb * 7din + #kifla * 9din treba je maksimizovati
# 1200min >= #hleb * 10min + #kifla * 12min
# 20000g >= #hleb * 300g + #kifla * 120g

# #hleb <= 1200min / 10min = 120
# #kifle <= 1200min / 12min = 100
# #hleb <= 20000g / 300g = 67
# #kifle <= 20000g / 120g = 167

# konacno:
# #hleb <= 67
# #kifle <= 100

problem = constraint.Problem()

problem.addVariable('#hleb', range(68))
problem.addVariable('#kifla', range(101))

problem.addConstraint(
        lambda x, y: 1200 >= 10*x + 12*y,
        ['#hleb', '#kifla']
)
problem.addConstraint(
        lambda x, y: 20000 >= 300*x + 120*y,
        ['#hleb', '#kifla']
)


max_profit = 0
max_solution = {}
for solution in problem.getSolutions():
    profit = 7*solution['#hleb'] + 9*solution['#kifla']
    print(profit, solution)
    if max_profit < profit:
        max_profit = profit
        max_solution = solution

print(max_profit, max_solution)

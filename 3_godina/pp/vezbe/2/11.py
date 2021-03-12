import constraint

# #radinka=250
# #elixir - broj radnika koji uce eliksir
# #dart - broj radnika koji uce dart

# gubitak(elixir) = 100e*#elixir
# gubitak(dart) = 105e*#dart

# dobit(elixir) = 150 * 5e * #elixir
# dobit(dart) = 170 * 6e * #dart

# 26000e >= 100e*#elixir + 105e*#dart
# 51200 >= 150*#elixir + 170*#dart
# 250 == #elixir + #dart

problem = constraint.Problem()

problem.addVariable('#Elixir', range(0, 251))
problem.addVariable('#Dart', range(0, 251))

problem.addConstraint(
        lambda e, d: e + d == 250,
        ['#Elixir', '#Dart']
)
problem.addConstraint(
        lambda e, d: 26000 >= 100*e + 105*d,
        ['#Elixir', '#Dart']
)
problem.addConstraint(
        lambda e, d: 51200 >= 150*e + 170*d,
        ['#Elixir', '#Dart']
)

max_solution = {}
max_profit = 0
for solution in problem.getSolutions():
    curr_profit = 150*5*solution['#Elixir'] + 170*6*solution['#Dart'] - (100*solution['#Elixir'] + 105*solution['#Dart'])
    if max_profit < curr_profit:
        max_profit = curr_profit
        max_solution = solution

print(max_profit, max_solution)



import constraint

problem = constraint.Problem()

# a b c
# d e f
# g h i

problem.addVariables('abcdefghi', range(1, 10))

problem.addConstraint(constraint.AllDifferentConstraint())
problem.addConstraint(lambda x, y, z: x + y + z == 15, 'abc')
problem.addConstraint(lambda x, y, z: x + y + z == 15, 'def')
problem.addConstraint(lambda x, y, z: x + y + z == 15, 'ghi')
problem.addConstraint(lambda x, y, z: x + y + z == 15, 'adg')
problem.addConstraint(lambda x, y, z: x + y + z == 15, 'beh')
problem.addConstraint(lambda x, y, z: x + y + z == 15, 'cfi')
problem.addConstraint(lambda x, y, z: x + y + z == 15, 'aei')
problem.addConstraint(lambda x, y, z: x + y + z == 15, 'ceg')

for r in problem.getSolutions():
    print(" -------")
    print("| {0:d} {1:d} {2:d} |".format(r['a'], r['b'],r['c']))
    print("| {0:d} {1:d} {2:d} |".format(r['d'],r['e'],r['f']))
    print("| {0:d} {1:d} {2:d} |".format(r['g'],r['h'],r['i']))
    print(" -------")

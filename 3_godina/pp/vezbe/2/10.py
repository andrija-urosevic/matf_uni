import constraint

#   A B C
#  D E F G
# H I J K L
#  M N O P
#   Q R S

constraint3 = lambda x, y, z: x + y + z == 38
constraint4 = lambda x, y, z, t: x + y + z + t == 38
constraint5 = lambda x, y, z, t, s: x + y + z + t + s== 38

problem = constraint.Problem()

problem.addVariables('ABCDEFGHIJKLMNOPQRS', range(1,20))

problem.addConstraint(constraint.AllDifferentConstraint())

problem.addConstraint(constraint3, 'ABC')
problem.addConstraint(constraint4, 'DEFG')
problem.addConstraint(constraint5, 'HIJKL')
problem.addConstraint(constraint4, 'MNOP')
problem.addConstraint(constraint3, 'QRS')

problem.addConstraint(constraint3, 'ADH')
problem.addConstraint(constraint4, 'BEIM')
problem.addConstraint(constraint5, 'CFJNQ')
problem.addConstraint(constraint4, 'GKOR')
problem.addConstraint(constraint3, 'LPS')

problem.addConstraint(constraint3, 'CGL')
problem.addConstraint(constraint4, 'BFKP')
problem.addConstraint(constraint5, 'AEJOS')
problem.addConstraint(constraint4, 'DINR')
problem.addConstraint(constraint3, 'HMQ')

for r in problem.getSolutions():
    print('---------------------')
    print('  {0} {1} {2}   '.format(r['A'], r['B'], r['C']))
    print(' {0} {1} {2} {3}  '.format(r['D'], r['E'], r['F'], r['G']))
    print('{0} {1} {2} {3} {4}'.format(r['H'], r['I'], r['J'], r['K'], r['L']))
    print(' {0} {1} {2} {3} '.format(r['M'], r['N'], r['O'], r['P']))
    print('  {0} {1} {2}   '.format(r['Q'], r['R'], r['S']))
    print('---------------------')

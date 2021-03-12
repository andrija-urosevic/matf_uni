import constraint

problem = constraint.Problem()

problem.addVariables('abcdeABDE', range(1,10))

problem.addConstraint(constraint.AllDifferentConstraint())
problem.addConstraint(
        lambda a, b, c, d, e, A, B, D, E:
            a < b < c < d < e and
            A < B < c < D < e and
            a + b + c + d + e == 25 and
            A + B + c + D + E == 25,
        'abcdeABDE'
)

for r in problem.getSolutions():
    print('−−−−−−−−−−−−−')
    print('{0:d}   {1:d}'. format(r['a'], r['A']))
    print(' {0:d} {1:d} '. format(r['b'], r['B']))
    print('  {0:d}      '. format(r['c']))
    print(' {0:d} {1:d} '. format(r['d'], r['D']))
    print('{0:d}   {1:d}'. format(r['e'], r['E']))
    print('−−−−−−−−−−−−−')


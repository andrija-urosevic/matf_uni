import cnf as f
import os

# Latin square order n: nXn matrix where each row and column contains each entry exactly onces.
# Greco-Latin square order n: pair of two latin squares of order n over two sets S and T (|S|=|T|=n)
#                             takav da nikoja dva polja ne sadrze isti par

def minisat_solve(problem_name, n, dimacs, number_to_var_name):
    with open(f'{problem_name}.cnf', 'w') as f:
        f.write(dimacs)

    os.system(f'minisat {problem_name}.cnf {problem_name}_result')
    with open(f'{problem_name}_result') as f:
        lines = f.readlines()

    if lines[0].startswith('SAT'):
        var_values = {}
        for var in lines[1].split(' ')[:-1]:
            var_number = int(var.strip('-'))
            var_name = number_to_var_name[var_number]
            var_values[var_name] = 0 if var.startswith('-') else 1
        valid_vars = list(filter(lambda x: x[1], var_values.items()))
        print(valid_vars)

        for i in range(n):
            for j in range(n):
                for k in range(1, n+1):
                    if var_values[f'A_{i}{j}{k}']:
                        print(chr(k-1 + 97), end='')
                        break
                for k in range(1, n+1):
                    if var_values[f'B_{i}{j}{k}']:
                        print(k, end=' ')
                        break
            print()



def greco_latin(n):
    cnf = f.CNF()

    # A_ijk <-> A(i,j) = k
    # B_ijk <-> B(i,j) = k

    # each latin square has entries from 1,...,n
    # A_ij1 V A_ij2 V ... V A_ijn
    # B_ij1 V B_ij2 V ... V B_ijn
    for i in range(n):
        for j in range(n):
            cnf.add_clause([f'A_{i}{j}{k}' for k in range(1,n+1)])
            cnf.add_clause([f'B_{i}{j}{k}' for k in range(1,n+1)])

    # each latin square has different entires
    # A_ijk => !A_ijk', k != k'
    # B_ijk => !B_ijk', k != k'
    for i in range(n):
        for j in range(n):
            for k1 in range(n):
                for k2 in range(n):
                    if k1 < k2:
                        cnf.add_clause([f'-A_{i}{j}{k1}', f'-A_{i}{j}{k2}'])
                        cnf.add_clause([f'-B_{i}{j}{k1}', f'-B_{i}{j}{k2}'])

    # each latin square has different entries in rows and columns
    # A_ijk => !A_i'jk, i != i'
    # B_ijk => !B_i'jk, i != i'
    # A_ijk => !A_ij'k, j != j'
    # B_ijk => !B_ij'k, j != j'
    for i1 in range(n):
        for i2 in range(n):
            if i1 < i2:
                for j in range(n):
                    for k in range(1, n+1):
                        cnf.add_clause([f'-A_{i1}{j}{k}', f'-A_{i2}{j}{k}'])
                        cnf.add_clause([f'-B_{i1}{j}{k}', f'-B_{i2}{j}{k}'])
                        cnf.add_clause([f'-A_{j}{i1}{k}', f'-A_{j}{i2}{k}'])
                        cnf.add_clause([f'-B_{j}{i1}{k}', f'-B_{j}{i2}{k}'])

    # no two entries are the same on same coordinates
    # For each pair (i,j) and (l,m) such that (i,j) != (l,m): A_ijk and B_ijk => !A_lmk V !B_lmk
    for i in range(n):
        for j in range(n):
            for l in range(n):
                for m in range(n):
                    if i != l and j != m:
                        for k in range(n):
                            cnf.add_clause([f'-A_{i}{j}{k}', f'-B_{i}{j}{k}', f'-A_{l}{m}{k}', f'-B_{l}{m}{k}'])


    minisat_solve('greco_latin', n, cnf.dimacs(), cnf.number_to_var_name)


if __name__ == '__main__':
    greco_latin(6)


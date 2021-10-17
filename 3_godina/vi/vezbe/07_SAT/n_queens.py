import cnf as f
import os

def minisat_solve(problem_name, n, dimacs, number_to_var_name):
    with open(f'{problem_name}.cnf', 'w') as f:
        f.write(dimacs)

    os.system(f'minisat {problem_name}.cnf {problem_name}_result')

    with open(f'{problem_name}_result') as f:
        lines = f.readlines()

    if lines[0].startswith("SAT"):
        print('Satisfiable')
        var_values = {}
        for var in lines[1].split(' ')[:-1]:
            var_number = int(var.strip('-'))
            var_name = number_to_var_name[var_number]
            var_values[var_name] = 0 if var.startswith('-') else 1

        print(var_values)

        print('  ', end='')
        print('----' * n)
        for i in range(n):
            print(i+1, '|', end='')
            for j in range(n):
                if var_values[f'p{i}{j}']:
                    print(' Q |', end='')
                else:
                    print('   |', end='')
            print()
            print('  ', end='')
            print('----' * n)

        print(end='    ')
        for i in range(n):
            print(i+1, end='   ')
    else:
        print('Unsatisfiable')



def n_queens(n):
    cnf = f.CNF()

    # each row has at least one queen
    for i in range(n):
        clause = [f'p{i}{j}' for j in range(n)]
        cnf.add_clause(clause)

    # each row has at most one queen
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if i != j:
                    cnf.add_clause([f'-p{k}{i}', f'-p{k}{j}'])

    # each colum has at least one queen
    for j in range(n):
        clause = [f'p{i}{j}' for j in range(n)]
        cnf.add_clause(clause)

    # each colum has at most one queen
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if i != j:
                    cnf.add_clause([f'-p{i}{k}', f'-p{j}{k}'])

    # there is no to queens diagonal
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for l in range(n):
                    if k > i and abs(i - k) == abs(j - l):
                        cnf.add_clause([f'-p{i}{j}', f'-p{k}{l}'])

    minisat_solve(f'{n}_queens', n, cnf.dimacs(), cnf.number_to_var_name)


if __name__ == '__main__':
    n_queens(8)



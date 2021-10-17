import cnf as f
import math
import os

def minisat_solver(problem_name, n, dimacs, number_to_var_name):
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
        print(sorted(valid_vars))

        print()
        for i in range(n):
            for j in range(n):
                for k in range(1, n+1):
                    if var_values[f'p_{i}{j}{k}']:
                        print(k, end=' ')
            print()


def same_subsquare(i1, j1, i2, j2, n):
    subsquare_size = int(math.sqrt(n))
    return i1 // subsquare_size == i2 // subsquare_size and \
           j1 // subsquare_size == j2 // subsquare_size


def sudoku(board_config):
    n = len(board_config)
    cnf = f.CNF()

    # p_ijk - board[i, j] = k
    for i in range(n):
        for j in range(n):
            k = board_config[i][j]
            if k != 0:
                cnf.add_clause([f'p_{i}{j}{k}'])

    # p_ijk, k in {1,...,n}
    for i in range(n):
        for j in range(n):
            clause = [f'p_{i}{j}{k}' for k in range(1, n+1)]
            cnf.add_clause(clause)

    # p_ijk != p_ijk', k != k'
    for i in range(n):
        for j in range(n):
            for k1 in range(1, n+1):
                for k2 in range(1, n+1):
                    if k1 < k2:
                        cnf.add_clause([f'-p_{i}{j}{k1}', f'-p_{i}{j}{k2}'])

    # p_ijk != p_i'jk, i != i'
    for i1 in range(n):
        for i2 in range(n):
            if i1 < i2:
                for j in range(n):
                    for k in range(1, n+1):
                        cnf.add_clause([f'-p_{i1}{j}{k}', f'-p_{i2}{j}{k}'])

    # p_ijk != p_ij'k, j != j'
    for i in range(n):
        for j1 in range(n):
            for j2 in range(n):
                if j1 < j2:
                    for k in range(1, n+1):
                        cnf.add_clause([f'-p_{i}{j1}{k}', f'-p_{i}{j2}{k}'])

    # p_ijk != p_i'j'k, same_subsquare(ij, i'j')
    for i1 in range(n):
        for i2 in range(n):
            if i1 < i2:
                for j1 in range(n):
                    for j2 in range(n):
                        if j1 < j2:
                            if same_subsquare(i1, j1, i2, j2, n):
                                cnf.add_clause([f'-p_{i1}{j1}{k}', f'-p_{i2}{j2}{k}'])

    minisat_solver(f'sudoku_{n}x{n}', n, cnf.dimacs(), cnf.number_to_var_name)


if __name__ == '__main__':
    board = [
        [8, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 3, 6, 0, 0, 0, 0, 0],
        [0, 7, 0, 0, 9, 0, 2, 0, 0],
        [0, 5, 0, 0, 0, 7, 0, 0, 0],
        [0, 0, 0, 0, 4, 5, 7, 0, 0],
        [0, 0, 0, 1, 0, 0, 0, 3, 0],
        [0, 0, 1, 0, 0, 0, 0, 6, 8],
        [0, 0, 8, 5, 0, 0, 0, 1, 0],
        [0, 9, 0, 0, 0, 0, 4, 0, 0]
    ]
    sudoku(board)

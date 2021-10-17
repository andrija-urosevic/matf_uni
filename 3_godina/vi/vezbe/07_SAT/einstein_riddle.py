import cnf as f
import os

def minisat_solve(problem_name, dimacs, number_to_var_name):
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
            var_values[var_name] = 0 if var[0] == '-' else 1

        true_values = \
            list(map(
                lambda x: x[0],
                sorted(list(filter(
                    lambda x: x[1],
                    var_values.items()))
                )
            ))
        print(true_values)


def solve_einstain_riddle():
    cnf = f.CNF()

    colors = ['red', 'green', 'white', 'yellow', 'blue']
    nations = ['Brit', 'Swede', 'Dane', 'Norwegian', 'German']
    pets = ['dogs', 'cats', 'horses', 'birds', 'fish']
    drinks = ['tea', 'coffe', 'milk', 'beer', 'water']
    cigarettes = ['Pall Mall', 'Blends', 'Dunhill', 'Blue Master', 'Prince']

    attributes = [colors, nations, pets, drinks, cigarettes]

    # assign each attribute a to some house
    for cat in attributes:
        for a in cat:
            cnf.add_clause([f'S_{i},{a}' for i in range(5)])

    # no two houses can have same attribute
    # S_i,a != S_j,a, i != j
    for cat in attributes:
        for a in cat:
            for i in range(5):
                for j in range(5):
                    if i < j:
                        cnf.add_clause([f'-S_{i},{a}', f'-S_{j},{a}'])

    # each house have at least one color, nation, pet, cigarette, drink
    for i in range(5):
        for cat in attributes:
            cnf.add_clause([f'S_{i},{a}' for a in cat])

    # each house cannot have two attributes from same category
    for cat in attributes:
        for a1 in cat:
            for a2 in cat:
                if a1 != a2:
                    for i in range(5):
                        cnf.add_clause([f'-S_{i},{a1}', f'-S_{i},{a2}'])

    # 1.  The Brit lives in the red house.
    # S_i,Brit => S_i,Red
    for i in range(5):
        cnf.add_clause([f'-S_{i},Brit', f'S_{i},red'])

    # 2.  The Swede keeps dogs as pets.
    # S_i,Swede => S_i,dogs
    for i in range(5):
        cnf.add_clause([f'-S_{i},Swede', f'S_{i},dogs'])

    # 3.  the dane drinks tea.
    # s_i,dane => s_i,tea
    for i in range(5):
        cnf.add_clause([f'-s_{i},dane', f's_{i},tea'])

    # 4.  The green house is next to the white house, on the left.
    # S_{i},green => S_{i+1},white
    for i in range(4):
        cnf.add_clause([f'-S_{i},green', f'S_{i+1},white'])

    # 5.  The owner of the green house drinks coffee.
    # S_{i},green => S_{i},coffee
    for i in range(5):
        cnf.add_clause([f'-S_{i},green', f'S_{i},coffee'])

    # 6.  The person who smokes Pall Mall rears birds.
    # S_{i},Pall Mall => S_{i},birds
    for i in range(5):
        cnf.add_clause([f'-S_{i},Pall Mall', f'S_{i},birds'])

    # 7.  The owner of the yellow house smokes Dunhill.
    # S_{i},yellow => S_{i},Dunhill
    for i in range(5):
        cnf.add_clause([f'-S_{i},yellow', f'S_{i},Dunhill'])

    # 8.  The man living in the centre house drinks milk.
    # S_3,milk
    cnf.add_clause([f'S_2,milk'])

    # 9.  The Norwegian lives in the first house.
    # S_1,Norwegian
    cnf.add_clause([f'S_0,Norwegian'])

    #10.  The man who smokes Blends lives next to the one who keeps cats.
    # S_{i},Blends => S_{i-1},cats V S_{i+1},cats
    # S_0,Blends => S_1,cats
    # S_4,Blends => S_3,cats
    for i in range(1, 4):
        cnf.add_clause([f'-S_{i},Blends', f'S_{i-1},cats', f'S_{i+1},cats'])
    cnf.add_clause([f'-S_0,Blends', f'S_1,cats'])
    cnf.add_clause([f'-S_4,Blends', f'S_3,cats'])

    #11.  The man who keeps horses lives next to the man who smokes Dunhill.
    # S_{i},horses => S_{i-1},Dunhill V S_{i+1},Dunhill
    # S_0,horses => S_1,Dunhill
    # S_4,horses => S_3,Dunhill
    for i in range(1, 4):
        cnf.add_clause([f'-S_{i},horses', f'S_{i-1},Dunhill', f'S_{i+1},Dunhill'])
    cnf.add_clause([f'-S_0,horses', f'S_1,Dunhill'])
    cnf.add_clause([f'-S_4,horses', f'S_3,Dunhill'])

    #12.  The man who smokes Blue Master drinks beer.
    # S_{i},Blue Master => S_{i},beer
    for i in range(5):
        cnf.add_clause([f'-S_{i},Blue Master', f'S_{i},beer'])

    #13.  The German smokes Prince.
    # S_{i},German => S_{i},Prince
    for i in range(5):
        cnf.add_clause([f'-S_{i},German', f'S_{i},Prince'])

    #14.  The Norwegian lives next to the blue house.
    # S_{i},Norwegian => S_{i-1},blue V S_{i+1},blue
    # S_0,Norwegian => S_1,blue
    # S_4,Norwegian => S_3,blue
    for i in range(1, 4):
        cnf.add_clause([f'-S_{i},Norwegian', f'S_{i-1},blue', f'S_{i+1},blue'])
    cnf.add_clause([f'-S_0,Norwegian', f'S_1,blue'])
    cnf.add_clause([f'-S_4,Norwegian', f'S_3,blue'])

    #15.  The man who smokes Blends has a neighbour who drinks water
    # S_{i},Blends => S_{i-1},water V S_{i+1},water
    # S_0,Blends => S_1,water
    # S_4,Blends => S_3,water
    for i in range(1, 4):
        cnf.add_clause([f'-S_{i},Blends', f'S_{i-1},water', f'S_{i+1},water'])
    cnf.add_clause([f'-S_0,Blends', f'S_1,water'])
    cnf.add_clause([f'-S_4,Blends', f'S_3,water'])

    minisat_solve('einstain_riddle', cnf.dimacs(), cnf.number_to_var_name)


if __name__ == '__main__':
    solve_einstain_riddle()

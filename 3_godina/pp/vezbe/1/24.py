def print_table(table):
    print('  0 1 2')
    for row in range(3):
        print(row, end=' ')
        for col in range(3):
            print(table[row][col], end=' ')
        print()

def check_table(table):
    for row in range(3):
        if table[row][0] == table[row][1] and\
           table[row][1] == table[row][2]:
            return table[row][0]
    for col in range(3):
        if table[0][col] == table[1][col] and\
           table[1][col] == table[2][col]:
            return table[0][col]
    if table[0][0] == table[1][1] and\
       table[1][1] == table[2][2]:
        return table[1][1]
    if table[0][2] == table[1][1] and\
       table[1][1] == table[2][0]:
        return table[1][1]
    return '-'

def play(player, action, table):
    if table[action[0]][action[1]] != '-':
        print('Odaberite validno polje za igranje!')
        return player
    table[action[0]][action[1]] = player
    if player == 'X':
        return 'O'
    else:
        return 'X'

print('IGRA X-O pocinje')
table = [['-' for _ in range(3)] for _ in range(3)]

name_A = input('Unesite ime prvog igraca:\n')
print(f'Zdravo {name_A}')
name_B = input('Unesite ime drugog igraca:\n')
print(f'Zdravo {name_B}')

player_A = ('X', name_A)
player_B = ('O', name_B)
print(f'{player_A}')
print(f'{player_B}')

print('Zapocnimo igru!')
print_table(table)

current_player = player_A
print(f'{current_player} na potezu!')
while True:
    row = int(input('Unesite red:\n'))
    col = int(input('Unesite kolonu:\n'))
    if play(current_player[0], (row, col), table) == 'X':
        current_player = player_A
    else:
        current_player = player_B
    print_table(table)
    winner = check_table(table)
    if winner == 'X':
        print(f'Pobednik je igrac {player_A}')
    elif winner == 'O':
        print(f'Pobednik je igrac {player_B}')
    if winner != '-':
        exit()
    print(f'{current_player} na potezu!')



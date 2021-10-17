import copy

def maximum(state):
    if end_state(state):
        return (evaluation_function(state), state)

    best_state_value = -float('inf')
    best_state = None
    for next_state in legal_sates(state):
        (next_state_value, _) = minimum(next_state)
        if best_state_value < next_state_value:
            best_state_value = next_state_value
            best_state = next_state

    return (best_state_value, best_state)

def minimum(state):
    if end_state(state):
        return (evaluation_function(state), state)

    best_state_value = float('inf')
    best_state = None
    for next_state in legal_sates(state):
        (next_state_value, _) = maximum(next_state)
        if best_state_value > next_state_value:
            best_state_value = next_state_value
            best_state = next_state

    return (best_state_value, best_state)


class XO(object):

    def __init__(self):
        super(XO, self).__init__()
        self.board = [['_' for i in range(0, 3)] for j in range(0, 3)]

        self.current_player = 'X'
        self.move_count = 0
        self.last_move = None

    def play_move(self, move):
        (i, j) = move
        assert self.board[i][j] == '_'
        self.board[i][j] = self.current_player
        self.current_player = 'X' if self.current_player == 'O' else 'O'
        self.move_count += 1
        self.last_move = move

    def draw_board(self):
        print(' '.join(self.board[0]))
        print(' '.join(self.board[1]))
        print(' '.join(self.board[2]))


def evaluation_function(game: XO):
    winner = get_winner(game)
    if winner == 'X':
        return 1
    if winner == 'O':
        return -1
    return 0

def legal_sates(game: XO):
    states = []
    for i in range(0, 3):
        for j in range(0, 3):
            if game.board[i][j] == '_':
                new_state = copy.deepcopy(game)
                new_state.play_move((i, j))
                states.append(new_state)

    return states

def get_next_user_move():
    i = int(input())
    j = int(input())
    return (i, j)

def get_next_computer_move(game: XO):
    _, state = minimum(game)
    return state.last_move

def end_state(game: XO):
    return get_winner(game) is not None or game.move_count == 9

def get_winner(game: XO):
    if game.board[0][0] == game.board[1][1] == game.board[2][2]:
        if game.board[1][1] != '_':
            return game.board[1][1]

    if game.board[0][2] == game.board[1][1] == game.board[2][0]:
         if game.board[1][1] != '_':
            return game.board[1][1]


    for i in range(0, 3):
        if game.board[i][0] == game.board[i][1] == game.board[i][2]:
            if game.board[i][1] != '_':
                return game.board[i][1]

    for j in range(0, 3):
        if game.board[0][j] == game.board[1][j] == game.board[2][j]:
            if game.board[1][j] != '_':
                return game.board[1][j]

    return None


if __name__ == '__main__':
    game = XO()
    game.draw_board()
    while True:
        next_move = get_next_user_move()
        game.play_move(next_move)
        game.draw_board()

        if get_winner(game) == 'X':
            print('Player X won!')
            break

        if end_state(game):
            print('Tie')
            break

        next_move = get_next_computer_move(game)
        game.play_move(next_move)
        game.draw_board()
        if get_winner(game) == 'O':
            print('Player O won!')
            break


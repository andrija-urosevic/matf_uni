from z3 import *

board=[".1111?1.",
       ".1?1222.",
       "12211?1.",
       "1?11221.",
       "1112?2..",
       "1112?31.",
       "1?113?31",
       "111.2???"]

WIDTH = len(board[0])
HEIGHT = len(board)

def check_board(row, col):

    s = Solver()
    cells = [[Int('r%d_c%d' % (r, c)) for c in range(WIDTH + 2)]
                for r in range(HEIGHT + 2)]

    for c in range(WIDTH + 2):
        s.add(cells[0][c] == 0)
        s.add(cells[HEIGHT + 1][c] == 0)

    for r in range(HEIGHT + 2):
        s.add(cells[r][0] == 0)
        s.add(cells[r][WIDTH+1] == 0)

    for r in range(1, HEIGHT + 1):
        for c in range(1, WIDTH + 1):
            s.add(Or(cells[r][c] == 0, cells[r][c] == 1))

            t = board[r - 1][c - 1]
            if t in '123456789':
                s.add(cells[r][c] == 0)
                s.add(cells[r - 1][c - 1] + cells[r - 1][c] + cells[r - 1][c + 1] +\
                      cells[r][c - 1] + cells[r][c] + cells[r][c + 1] +\
                      cells[r + 1][c - 1] + cells[r + 1][c] + cells[r + 1][c + 1]\
                      == int(t))

    s.add(cells[row][col] == 1)

    if s.check() == unsat:
        print("unsat: row=%d col=%d" % (row, col))


for row in range(1, HEIGHT + 1):
    for col in range(1, WIDTH + 1):
        if board[row - 1][col - 1] == "?":
            check_board(row, col)

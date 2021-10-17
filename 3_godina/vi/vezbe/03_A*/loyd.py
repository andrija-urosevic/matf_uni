from queue import PriorityQueue
from collections import defaultdict

import copy
import time

def print_state(state):
    for row in state_to_mat(state):
        for it in row:
            print(f'{it:4}', end='')
        print()
    print()

def state_to_mat(state):
    arr = state.split(',')
    return [[int(arr[i]) for i in range(j*4, j*4 + 4)] for j in range(0,4)]


def mat_to_state(mat):
    state = []
    for row in mat:
        for it in row:
            state.append(str(it))
    return ','.join(state)


def h(state):

    def manhetn_dist(i, j, val):
        if val == 0:
            val = 16
        val -= 1
        return abs(val % 4 - j) + abs(val // 4 - i)


    sum_manhetn_dist = 0
    mat = state_to_mat(state)
    for i in range(0, 4):
        for j in range(0, 4):
            sum_manhetn_dist += manhetn_dist(i, j, mat[i][j])
    return sum_manhetn_dist


end_state = lambda : '1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,0'


def gen_path(pi, start_state, end_state):
    print('Path found:')
    path = []
    while pi[end_state]:
        path.append(end_state)
        end_state = pi[end_state]
    path.append(start_state)
    path.reverse()
    return path


def gen_next_state(state):
    mat = state_to_mat(state)

    empty_i = 0
    empty_j = 0

    for i in range(0,4):
        for j in range(0,4):
            if mat[i][j] == 0:
                empty_i = i
                empty_j = j
                break

    up_mat = copy.deepcopy(mat)
    down_mat = copy.deepcopy(mat)
    left_mat = copy.deepcopy(mat)
    right_mat = copy.deepcopy(mat)

    if empty_j > 0:
        up_mat[empty_i][empty_j], up_mat[empty_i][empty_j-1] =\
            mat[empty_i][empty_j-1], 0

    if empty_j < 3:
        down_mat[empty_i][empty_j], down_mat[empty_i][empty_j+1] =\
            mat[empty_i][empty_j+1], 0

    if empty_i > 0:
        left_mat[empty_i][empty_j], left_mat[empty_i-1][empty_j] =\
            mat[empty_i-1][empty_j], 0

    if empty_i < 3:
        right_mat[empty_i][empty_j], right_mat[empty_i+1][empty_j] =\
            mat[empty_i+1][empty_j], 0

    return map(mat_to_state, [up_mat, down_mat, left_mat, right_mat])


def astar(start_state):
    pi = {}
    pi[start_state] = None

    g = defaultdict(lambda : float('inf'))
    g[start_state] = 0

    f = defaultdict(lambda : float('inf'))
    f[start_state] = g[start_state] + h(start_state)

    open_list = PriorityQueue()
    open_list.put((f[start_state], start_state))

    while not open_list.empty():
        current_f, current_state = open_list.get()

        if current_state == end_state():
            return gen_path(pi, start_state, end_state())

        for next_state in gen_next_state(current_state):
            print_state(next_state)
            print()
            if g[next_state] > g[current_state] + 1:
                g[next_state] = g[current_state] + 1
                f[next_state] = g[next_state] + h(next_state)
                pi[next_state] = current_state
                open_list.put((f[next_state], next_state))

    return None

if __name__ == '__main__':
    print('Loyd\'s 15 puzzle:\n')

    for state in astar('5,1,2,4,7,6,3,8,9,10,11,12,13,14,15,0'):
        time.sleep(2)
        print_state(state)


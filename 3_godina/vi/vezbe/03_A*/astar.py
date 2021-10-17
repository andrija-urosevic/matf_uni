import json
from queue import PriorityQueue
from collections import defaultdict

def get_path(pi, start_node, end_node):
    path = []
    while end_node != start_node:
        path.append(end_node)
        end_node = pi[end_node]
    path.append(start_node)
    path.reverse()
    return path


def astar(adj_list, start_node, end_node, h):
    pi = {}
    pi[start_node] = None

    g = defaultdict(lambda : float('inf'))
    g[start_node] = 0

    f = defaultdict(lambda : float('inf'))
    f[start_node] = g[start_node] + h[start_node]

    open_list = PriorityQueue()
    open_list.put((f[start_node], start_node))

    while not open_list.empty():
        current_f, current_node = open_list.get()

        if current_node == end_node:
            return get_path(pi, start_node, end_node)

        for next_node, cost in adj_list[current_node]:
            if g[next_node] > g[current_node] + cost:
                g[next_node] = g[current_node] + cost
                f[next_node] = g[next_node] + h[next_node]
                pi[next_node] = current_node
                open_list.put((f[next_node], next_node))

    return None


if __name__ == '__main__':

    with open('cities.json') as f:
        adj_list = json.load(f)

    with open('cities_heuristics.json') as f:
        h = json.load(f)

    print(astar(adj_list, 'Arad', 'Buchares', h))


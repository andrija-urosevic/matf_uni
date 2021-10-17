import json
from queue import Queue

def breath_first_traversal(adj_list, start_node):
    levels = [[]]
    visited = set()
    queue = Queue()

    visited.add(start_node)
    queue.put(start_node)
    queue.put(None)

    while not queue.empty():
        current_node = queue.get()
        if current_node == None:
            if queue.empty():
                break
            queue.put(None)
            levels.append([])
            continue
        levels[-1].append(current_node)
        for next_node, _ in adj_list[current_node]:
            if next_node not in visited:
                visited.add(next_node)
                queue.put(next_node)

    return levels

def breath_first_search(adj_list, start_node, end_node):
    visited = set()
    queue = Queue()

    visited.add(start_node)
    queue.put(start_node)

    parent = dict()
    parent[start_node] = None

    path_found = False
    while not queue.empty():
        current_node = queue.get()
        if current_node == end_node:
            path_found = True
            break
        for next_node, _ in adj_list[current_node]:
            if next_node not in visited:
                parent[next_node] = current_node
                visited.add(next_node)
                queue.put(next_node)

    if path_found:
        path = []
        path.append(end_node)
        while parent[end_node] is not None:
            end_node = parent[end_node]
            path.append(end_node)
        return path

    return None


if __name__ == '__main__':
    with open('cities.json') as f:
        adj_list = json.load(f)
        print(adj_list)
        levels = breath_first_traversal(adj_list, 'Oradea')
        print(levels)

        path = breath_first_search(adj_list, 'Oradea', 'Lasi')
        print(path)

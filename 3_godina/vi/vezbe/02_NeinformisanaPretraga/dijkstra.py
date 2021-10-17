import json
from queue import PriorityQueue

def dijkstra(adj_list, start_node, end_node):
    visited = set()
    dist = {node : float('inf') for node in adj_list}
    dist[start_node] = 0

    min_heap = PriorityQueue()
    min_heap.put((0, start_node))

    parent = {}
    parent[start_node] = None

    path_found = False
    while not min_heap.empty():
        (current_dist, current_node) = min_heap.get()
        visited.add(current_node)

        if current_node == end_node:
            path_found = True
            break

        for (next_node, next_dist) in adj_list[current_node]:
            if next_node not in visited:
                if dist[next_node] > dist[current_node] + next_dist:
                    dist[next_node] = dist[current_node] + next_dist
                    parent[next_node] = current_node
                    min_heap.put((dist[next_node], next_node))

    if path_found:
        path = []
        final_dist = dist[end_node]
        path.append(end_node)
        while parent[end_node] is not None:
            end_node = parent[end_node]
            path.append(end_node)
        return final_dist, path

    return None

if __name__ == '__main__':
    with open('cities.json') as f:
        adj_list = json.load(f)
        print(dijkstra(adj_list, 'Oradea', 'Drobeta'))



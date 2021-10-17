import json

def depth_first_traversal(adj_list, start_node, traversal, visited = set()):
    if start_node in visited:
        return

    visited.add(start_node)
    traversal.append(start_node)

    for next_node, _ in adj_list[start_node]:
        if next_node not in visited:
            depth_first_traversal(adj_list, next_node, traversal, visited)

def depth_first_search(adj_list, start_node, end_node, path, visited = set()):
    path.append(start_node)

    if start_node == end_node:
        return path

    visited.add(start_node)

    for next_node, _ in adj_list[start_node]:
        if next_node not in visited:
            result =  depth_first_search(adj_list, next_node, end_node, path, visited)
            if result is not None:
                return result

    path.pop()
    return None

if __name__ == '__main__':
    with open('cities.json') as f:
        adj_list = json.load(f)
        traversal = []
        depth_first_traversal(adj_list, 'Oradea', traversal)
        print(traversal)

        path = []
        depth_first_search(adj_list, 'Drobeta', 'Lugoj', path)
        print(path)


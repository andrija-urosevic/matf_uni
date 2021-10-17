def Max(evaluation_function, valid_states, current_state,
        depth=float('inf'), alpha=float('-inf'), beta=float('inf')):

    if depth <= 0 or end_state(current_state):
        return evaluation_function(current_state), current_state

    best_next_state = None
    best_next_value = float('-inf')

    for next_state in valid_states(current_state):
        next_value, _ = Min(evaluation_function, next_state, depth - 1)
        if best_next_value < next_value:
            best_next_value = next_value
            best_next_state = next_state
        if alpha < best_next_value:
            alpha = best_next_value
        if beta <= best_next_value:
            return best_next_value, best_next_state

    return best_next_value, best_next_state


def Min(evaluation_function, valid_states, current_state,
        depth=float('inf'), alpha=float('-inf'), beta=float('inf')):

    if depth <= 0 or end_state(current_state):
        return evaluation_function(current_state), current_state

    best_next_state = None
    best_next_value = float('+inf')

    for next_state in valid_states(current_state):
        next_value, _ = Min(evaluation_function, next_state, depth - 1)
        if best_next_value > next_value:
            best_next_value = next_value
            best_next_state = next_state
        if beta > best_next_value:
            beta = best_next_state
        if alpha >= best_next_value:
            return best_next_value, best_next_state

    return best_next_value, best_next_state

def Minimax(current_state):

    def evaluation_function(state):
        return 0
    def valid_state(state):
        return []

    return Max(evaluation_function, valid_stete, current_state, depth=10)


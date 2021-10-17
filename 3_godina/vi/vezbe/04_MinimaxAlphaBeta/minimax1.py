def Max(evaluation_function, current_state, depth=float('inf')):

    if depth <= 0 or end_state(current_state):
        return evaluation_function(current_state)

    best_next_state = None
    best_next_value = float('-inf')

    for next_state in valid_state(current_state):
        next_value, _ = Min(evaluation_function, next_state, depth - 1)
        if best_next_value < next_value:
            best_next_value = next_value
            best_next_state = next_state

    return best_next_value, best_next_state


def Min(evaluation_function, current_state, depth=float('inf')):

    if depth <= 0 or end_state(current_state):
        return evaluation_function(current_state), current_state

    best_next_state = None
    best_next_value = float('+inf')

    for next_state in valid_state(current_state):
        next_value, _ = Min(evaluation_function, next_state, depth - 1)
        if best_next_value > next_value:
            best_next_value = next_value
            best_next_state = next_state

    return best_next_value, best_next_state

def Minimax(evaluation_function, current_state):
    return Max(evaluation_function, current_state, depth=10)


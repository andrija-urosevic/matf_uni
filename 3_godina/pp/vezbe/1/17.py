def max_list(lst):
    m = lst[-1]
    for el in lst:
        if m < el:
            m = el
    return m

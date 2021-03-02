def max_list(lst):
    m = list[-1]
    for el in lst:
        if m < el:
            m = el
    return m

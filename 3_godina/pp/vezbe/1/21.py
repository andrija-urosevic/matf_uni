def min_torki(torke):
    m = torke[0]
    for torka in torke:
        if m > torka:
            m = torka
    return m

torke = ((1,2,'c'), (1,2,'b'), (2,2,'5'))
print(min_torki(torke))



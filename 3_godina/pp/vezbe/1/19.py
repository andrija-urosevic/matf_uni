n = int(input())
mapa = {}
for x in range(n):
    mapa[x] = x**2


for it, val in mapa.items():
    print(f'f({it}) = {val}')



import json
import math

def dist(A):
    return math.sqrt(A[0]**2 + A[1]**2)

with open('tacke.json', 'r') as file:
    data = json.load(file)

sorted_data = sorted(data, key=lambda x: dist(x['koordinate']))

print('Nesortirana temena:', end=' ')
for point in data:
    print(point['teme'], end=' ')

print('\nSortirana temena:', end=' ')
for point in sorted_data:
    print(point['teme'], end=' ')


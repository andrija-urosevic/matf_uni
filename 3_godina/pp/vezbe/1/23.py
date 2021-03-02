import random
import math

def dist(A, B):
    return math.sqrt((A[0] - B[0])**2 + (A[1] - B[1])**2)

def in_circle(A):
    return dist(A,(0.5, 0.5)) <= 0.5

print('Izrazunavanje broja PI metodom Monte Karlo')
n = int(input('Unesite broj iteracija:\n'))

count = 0
for _ in range(n):
    A = (random.random(), random.random())
    print('Tacka:', A)
    if in_circle(A):
        count += 1

pi = 4 * count / n
print(f'Broj PI aproksiran metodom Monte Karlo: {pi}')



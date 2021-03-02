def empty(x, y, z):
    pass

def square(x):
    return x ** 2

def translation(x):
    return x - 1

print(empty, square, translation, sep='\n')
print(empty(1, 2, 3))
print(square(3))
print(translation(3))
print(translation(square(3)))

print('Anonimne funkcije')
square = lambda x: x ** 2
translation = lambda x: x - 1

print(square, translation, sep='\n')
print(square(3))
print(translation(3))
print(translation(square(3)))


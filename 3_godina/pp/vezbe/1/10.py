def translate_mutable(l):
    l[0] = 'A'

def translate_imutable(l):
    l = l[:-1]

l = [1, 2, 3, 4]

print(l)
print('Imutable function!')
translate_imutable(l)
print(l)

print('Mutable function!')
translate_mutable(l)
print(l)

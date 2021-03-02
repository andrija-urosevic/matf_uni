try:
    n = int(input('Unesite ceo broj: '))
except ValueError:
    print('Nije unet ceo broj')
    exit()

hello = 'hello world'
print(hello, id(hello))
world = 'hello world'
print(world, id(world))
print(hello == world)
# hello[3] = 'a'

import random

def gen_num():
    return random.randint(0, 100)

def hit_test(num, test_num):
    if num < test_num:
        print('Broj koji sam zamislio je MANJI od', test_num)
    elif num > test_num:
        print('Broj koji sam zamislio je VECI od', test_num)
    else:
        print(f'BRAVO!!! Pogodio si! Zamislio sam {num}.')
        print('Bilo je lepo igrati se sa tobom')
        exit()

print('------------- IGRA: Pogodi broj -------------')

num = gen_num()

ime = input('Unesite vase ime:\n')
print('Zdravo', ime, ':)')

while True:
    test_num = int(input('Unesi broj:\n'))
    hit_test(num, test_num)

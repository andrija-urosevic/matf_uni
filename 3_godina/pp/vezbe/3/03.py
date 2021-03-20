imena = ['Marko', 'Petar', 'Pavle']
ocene = [int(input(f'Unesite ocenu za {ime}:')) for ime in imena]

ime_ocena = zip(imena, ocene)


for ime, ocena in ime_ocena:
    print(ime, ocena)

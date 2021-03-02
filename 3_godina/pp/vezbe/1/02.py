x = int(input('Unesite ceo broj: '))
y = int(input('Unesite ceo broj: '))
s = input('Unesite nisku: ')

print(f'Celi brojevi {x} i {y}, niska {s}')

zbir = x + y
razlika = x - y
proizvod = x * y
kolicnik = x / y
stepen = x ** y
deljenje = x // y

print(f'Zbir {zbir:d}, razlika {razlika:d},',\
      f'proizvod {proizvod:d}, kolicnik {kolicnik:f},',\
      f'stepen {stepen:f}, deljenje {deljenje:d}')


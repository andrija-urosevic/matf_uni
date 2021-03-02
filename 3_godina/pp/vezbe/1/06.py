def radni_dan(dan):
    if dan % 7 == 0 or dan % 7 == 6:
        return False
    return True

for i in range(10):
    try:
        dan = int(input('Unesite dan: '))
    except ValueError:
        print('Neispravan dan!')
        exit()
    if radni_dan(dan):
        print('Unet je radni dan!')
    else:
        print('Unet je neradni dan!')

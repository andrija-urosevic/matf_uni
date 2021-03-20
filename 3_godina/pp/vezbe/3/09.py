import json

with open('knjige.json') as f:
    knjige = json.load(f)

def cena_knjige(knjiga):
    trenutna_cena = knjiga['cena'] * knjiga['kolicina']
    if trenutna_cena >= 100.0:
        return trenutna_cena
    return trenutna_cena + 10.0


oznaka_cena = [(knjiga['oznaka'], cena_knjige(knjiga)) for knjiga in knjige]
print(oznaka_cena)


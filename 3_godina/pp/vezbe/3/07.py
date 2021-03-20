import json
from functools import reduce

with open('korpa.json') as f:
    korpa = json.load(f)

with open('maksi_cene.json') as f:
    maksi_cene = json.load(f)

with open('idea_cene.json') as f:
    idea_cene = json.load(f)

with open('shopngo_cene.json') as f:
    shopngo_cene = json.load(f)

print(korpa)
print(maksi_cene)
print(idea_cene)
print(shopngo_cene)

cena_maksi = 0.0
for it in korpa:
    ime_artikla = it['ime']
    kolicna_artikla = it['kolicina']
    for artikl in maksi_cene:
        if artikl['ime'] == ime_artikla:
            cena_maksi += artikl['cena'] * kolicna_artikla

def cena(ime_artikla, prodavnica):
    for artikl in prodavnica:
        if artikl['ime'] == ime_artikla:
            return artikl['cena']

racun_maksi = sum([it['kolicina'] * cena(it['ime'], maksi_cene) for it in korpa])
racun_idea = sum([it['kolicina'] * cena(it['ime'], idea_cene) for it in korpa])
racun_shopngo = sum([it['kolicina'] * cena(it['ime'], shopngo_cene) for it in korpa])

print(racun_maksi)
print(racun_idea)
print(racun_shopngo)

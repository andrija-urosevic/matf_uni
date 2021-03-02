import json

with open('korpa.json', 'r') as file:
    korpa = json.load(file)

with open('maksi_cene.json', 'r') as file:
    maksi = json.load(file)

with open('idea_cene.json', 'r') as file:
    idea = json.load(file)

with open('shopngo_cene.json', 'r') as file:
    shopngo = json.load(file)

maksi_cena = 0
idea_cena = 0
shopngo_cena = 0
for item in korpa:
    for prod in maksi:
        if prod['ime'] == item['ime']:
            maksi_cena += item['kolicina'] * prod['cena']

    for prod in idea:
        if prod['ime'] == item['ime']:
            idea_cena += item['kolicina'] * prod['cena']

    for prod in shopngo:
        if prod['ime'] == item['ime']:
            shopngo_cena += item['kolicina'] * prod['cena']

print(f'Maksi: {maksi_cena}')
print(f'Idea: {idea_cena}')
print(f'Shopngo: {shopngo_cena}')

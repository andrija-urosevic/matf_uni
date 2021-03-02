import json

with open('datoteka.txt', 'r') as f:
    x = json.load(f)
    print(x['Ime'])
    print(x['Prezime'])
    print(x['Godine'])

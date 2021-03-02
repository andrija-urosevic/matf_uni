import json

firstname = input('Ime: ')
lastname = input('Prezime: ')
year = input('Godine: ')

guy = {'Ime': firstname, 'Prezime': lastname, 'Godine': year}
print(json.dumps(guy))

with open('datoteka.txt', 'w') as f:
    json.dump(guy, f)

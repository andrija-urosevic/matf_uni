import json
from datetime import datetime

with open('radnici.json', 'r') as file:
    radnici = json.load(file)

curtime = datetime.now()

opcija = input('Unesite opciju!\nd - dostupni radnici\no - radnici na odmoru\n')

if opcija == 'd':
    for radnik in radnici:
        pocetak_radnog_vremena = datetime.strptime(radnik['radno_vreme'][0], "%H:%M").time()
        kraj_radnog_vremena = datetime.strptime(radnik['radno_vreme'][1], "%H:%M").time()
        if pocetak_radnog_vremena <= curtime.time() and curtime.time() <= kraj_radnog_vremena:
            print(radnik['ime'])

elif opcija == 'o':
    for radnik in radnici:
        pocetak_odmora = datetime.strptime(radnik['odmor'][0], "%d.%m.%Y.").date()
        kraj_odmora = datetime.strptime(radnik['odmor'][1], "%d.%m.%Y.").date()
        if pocetak_odmora <= curtime.date() and curtime.date() <= kraj_odmora:
            print(radnik['ime'])

else:
    print('Uneta opcija nije podrzana')

import json
from datetime import datetime

with open('utakmice.json') as f:
    utakmice = json.load(f)

def u_vremenskom_intervalu(utakmice, pocetak, kraj):
    return [utakmica for utakmica in utakmice if pocetak <= datetime.strptime(utakmica['Vreme'], "%H:%M") <= kraj]

pocetak = datetime.strptime(input('Vreme pocetka: '), "%H:%M")
kraj = datetime.strptime(input('Vreme kraja: '), "%H:%M")

print(u_vremenskom_intervalu(utakmice, pocetak, kraj))


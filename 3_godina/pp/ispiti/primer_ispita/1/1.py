import json
import sys

class Player(object):
    def __init__(self, dres, ime, prezime, visina, godine):
        self.dres = dres
        self.ime = ime
        self.prezime = prezime
        self.visina = visina
        self.godine = godine
        self.calc_pozicija()

    def calc_pozicija(self):
        if self.visina >= 200:
            self.pozicija = 5
        elif self.visina <= 190:
            self.pozicija = 1
        else:
            self.pozicija = 3

    def validan(self, pozicija, godine):
        return self.pozicija == pozicija and self.godine <= godine



if __name__ == '__main__':
    if len(sys.argv) != 2:
        print('Nedovoljno argumenata')
        exit()
    filename = sys.argv[1]
    godine = float(input())
    pozicija = int(input())

    tim = []
    with open(filename, 'r') as f:
        igraci = json.load(f)
        for igrac in igraci:
            kandidat = Player(igrac['dres'], igrac['ime'], igrac['prezime'], igrac['visina'], igrac['godine'])
            tim.append(kandidat)

    tim = list(filter(lambda x: x.validan(pozicija, godine), tim))
    if len(tim) > 0:
        igrac = max(tim, key=lambda x: x.visina)
        print(igrac.visina)
    else:
        print(-1)

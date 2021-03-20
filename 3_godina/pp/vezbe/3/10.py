import json
import sys
from functools import cmp_to_key

uporedi = lambda x, y: -1 if x['Golovi'] < y['Golovi'] else 1 if x['Golovi'] > y['Golovi'] else 0

if len(sys.argv) != 3:
    exit('Argumenti')

nacionalnost = sys.argv[1]
fudbaleri_filename = sys.argv[2]

with open(fudbaleri_filename) as f:
    fudbaleri = json.load(f)

nacionalnost_fudbaleri = list(filter(lambda x: x['Nacionalnost'] == nacionalnost, fudbaleri))
sortirani_fudbaleri = sorted(nacionalnost_fudbaleri, key=cmp_to_key(uporedi))

with open(nacionalnost + '_nacionalnost.json', 'w') as f:
    json.dump(sortirani_fudbaleri, f)

import os
import json

dirname = input('Unesite putanju do direktorijuma: ')

ext_map = {}
for root, dirs, files in os.walk(dirname):
    for filename in files:
        i = filename[::-1].find('.')
        ext = filename[-i:]
        if ext in ext_map:
            ext_map[ext] += 1
        else:
            ext_map[ext] = 1

with open('rezultat.json', 'w') as f:
    json.dump(ext_map, f)


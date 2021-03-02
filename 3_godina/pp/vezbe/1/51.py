import json
import re

filename = input('Unesite ime datoteke: ')

with open(filename, 'r') as file:
    data = ''.join(file.readlines())

oneline = re.compile(r'//\s+(.*)')
multiline = re.compile(r'/\*\s+(.*?)\s+\*/', re.DOTALL)

comments = {'oneline': [], 'multiline': []}

for m in oneline.finditer(data):
    comments['oneline'].append(m.group(1))

for m in multiline.finditer(data):
    comments['multiline'].append(m.group(1))

with open('komentari.json', 'w') as file:
    json.dump(comments, file)

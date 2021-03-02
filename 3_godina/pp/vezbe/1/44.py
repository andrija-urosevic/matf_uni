import json

filename = input('Unesite ime datoteke: ')
n = int(input('Unesite broj n: '))

with open(filename, 'r') as file:
    data = ''.join(file.readlines())
    print(data)

ngram_count = {}
for i in range(len(data) - n):
    ngram = data[i:i+n]
    if ngram in ngram_count:
        ngram_count[ngram] += 1
    else:
        ngram_count[ngram] = 1

with open('rezultat.json', 'w') as res:
    json.dump(ngram_count, res)


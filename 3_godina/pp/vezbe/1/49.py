import os

filename = input('Unesite ime datoteke: ')

for root, dirs, files in os.walk('/'):
    for file in files:
        if file == filename:
            print(os.path.join(root, file))

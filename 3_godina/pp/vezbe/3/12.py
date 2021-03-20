import os

word = input('Unesite red: ')

def has_word(file):
    with open(file) as f:
        if word in f.read():
            return True
    return False

files = [os.path.join(root, file) for root, dirs, files in os.walk('../..') for file in files]

files_word = list(filter(has_word, files))
print(list(map(lambda x: os.path.realpath(x), files_word)))


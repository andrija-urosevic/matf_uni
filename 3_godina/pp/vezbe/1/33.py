with open('datoteka.txt', 'r') as f:
    print(f)
    for line in f.readlines():
        print(line, end='')

print('---------------------------')

with open('datoteka.txt', 'a+') as f:
    f.write('water\n')
    f.seek(0, 0)
    for line in f.readlines():
        print(line, end='')

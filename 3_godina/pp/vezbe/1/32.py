str1 = input('Unesite nisku1: ')
str2 = input('Unesite nisku2: ')

if len(str1) >= len(str2):
    i = str1.find(str2)
    if i == -1:
        print('-'.join([str1, str2]))
    else:
        str1 = str1[0:i] + '$' + str1[i+len(str2):]
        print(str1)
else:
    print(f'Duzina niske {str1} je {len(str1)}')

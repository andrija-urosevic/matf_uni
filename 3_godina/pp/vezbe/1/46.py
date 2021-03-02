import os

dirpath = input('Unesite putanju do direktorijuma')

long_files = 0
fat_files = 0
for root, dirs, files in os.walk(dirpath):
    for file in files:
        filename = os.path.join(root, file)
        with open(filename) as f:
            file_max_line = 0
            file_len = 0
            for line in f.readlines():
                file_len += 1
                if file_max_line < len(line):
                    file_max_line = len(line)
            if file_len < file_max_line:
                fat_files += 1
            else:
                long_files += 1


print(f'Odnos skupa duze i skupa sire je: {long_files}:{fat_files}')

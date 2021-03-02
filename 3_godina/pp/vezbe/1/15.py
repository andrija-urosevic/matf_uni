buffer = []
while True:
    line = input()
    if line == 'quit':
        break
    buffer.append(line)
    if len(buffer) == 5:
        for it in buffer:
            print(it)
        buffer = []

import os

print(os.listdir(os.curdir))

for (root, dirs, files) in os.walk(os.curdir):
    print(root)
    for file in files:
        print(os.path.join(root, file))

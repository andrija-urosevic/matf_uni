import math
import random
import sys
import os
import time
import re

print(math.factorial(21))
print(math.log(1340, 10))

print(random.random())
print(random.randint(0, 10))

print(sys.argv)

os.system('ls -all')

print(time.time())

broj = input('Unesite string: ')
print(re.search(r'[-+]?[0-9]+', broj)[0])

def printf(*x):
    print(x)

printf()
printf(1)
printf([1,2,3])
printf(2, 'test1', [1,2,3])

def printf(**x):
    print(x)

printf()
printf(x=1)
printf(test=[1,2,3])
printf(id=2, str='test1', lst=[1,2,3])

def aritmeticka_sredina(*xs):
    s = sum(xs)
    n = len(xs)
    return s / n

aritmeticka_sredina(1, 2, 3, 4)


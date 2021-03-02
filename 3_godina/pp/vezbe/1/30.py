class MyIterator(object):

    def __init__(self, limit):
        self.limit = limit

    def __iter__(self):
        self.x = 0
        return self

    def __next__(self):
        x = self.x
        if x > self.limit:
            raise StopIteration
        else:
            self.x += 1
            return x

for i in MyIterator(10):
    print(i)

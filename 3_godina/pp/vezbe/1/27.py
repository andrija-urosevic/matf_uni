class Stack(object):

    def __init__(self):
        self.stack = []

    def push(self, el):
        self.stack.append(el)

    def pop(self):
        try:
            return self.stack.pop()
        except IndexError:
            print('Stek je prazan!')
            return None

    def peek(self):
        try:
            return self.stack[-1]
        except IndexError:
            print('Stek je prazan!')
            return None

stack = Stack()
stack.push(2)
stack.push(5)
stack.push(1)
print(stack.peek())
print(stack.pop())
print(stack.pop())
print(stack.pop())
print(stack.pop())
print(stack.peek())



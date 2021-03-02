import math

class Shape(object):

    def __init__(self, color='Black', padding=False):
        self.__color='Black'
        self.__padding=False

    def get_color(self):
        return self.__color

    def get_padding(self):
        return self.__padding

    def set_padding(self, padding):
        self.__padding = padding

class Rect(Shape):

    def __init__(self, a, b):
        super().__init__(color='Red')
        self.__a = a
        self.__b = b

    def area(self):
        return self.__a * self.__b

    def parimeter(self):
        return 2 * (self.__a + self.__b)

class Circle(Shape):

    def __init__(self, r):
        super().__init__(color='Blue')
        self.__r = r

    def area(self):
        return math.pi * self.__r **2

    def parimeter(self):
        return 2 * math.pi * self.__r

class Point(object):

    def __init__(self, x, y):
        self.x = x
        self.y = y

    def __str__(self):
        return "({0}, {1})".format(self.x, self.y)

    def __add__(self, other):
        x = self.x + other.x
        y = self.y + other.y
        return Point(x, y)


rect = Rect(10.5, 2.5)
rect.set_padding(True)
print(f'Area of rect: {rect.area()}')
print(f'Parimeter of rect: {rect.parimeter()}')
print(f'Color of rect: {rect.get_color()}')
print(f'Padding of rect: {rect.get_padding()}')

circ = Circle(10)
print(f'Area of circle: {circ.area()}')
print(f'Parimeter of cirlcle: {circ.parimeter()}')
print(f'Color of circle: {circ.get_color()}')
print(f'Padding of circle: {circ.get_padding()}')

p1 = Point(10, 10)
p2 = Point(2, 1)
print(f'Sum of point A{p1} and B{p2} is A+B{p1 + p2}')



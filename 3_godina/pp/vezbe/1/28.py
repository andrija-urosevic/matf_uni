class Robot(object):

    population = 0

    def __init__(self, name):
        self.name = name
        Robot.population += 1
        print(f'{self.name} is created!')

    def __del__(self):
        Robot.population -= 1
        print(f'{self.name} is destroyed!')

    def say_hi(self):
        print(f'Hi, my name is {self.name}!')

    @classmethod
    def get_population(cls):
        print(f'There is {cls.population} active robots!')

droid1 = Robot('D2B2')
droid1.say_hi()
Robot.get_population()

droid2 = Robot('D2B8')
droid2.say_hi()
Robot.get_population()

del droid1
del droid2

Robot.get_population()

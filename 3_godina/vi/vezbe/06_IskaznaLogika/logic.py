from itertools import combinations
import copy


class Formula(object):

    def __init__(self):
        pass

    def __invert__(self):
        return Not(copy.deepcopy(self))

    def __and__(self, A):
        return And(copy.deepcopy(self), copy.deepcopy(A))

    def __or__(self, A):
        return Or(copy.deepcopy(self), copy.deepcopy(A))

    def __rshift__(self, A):
        return Impl(copy.deepcopy(self), copy.deepcopy(A))

    def __eq__(self, A):
        return Eq(copy.deepcopy(self), copy.deepcopy(A))

    def __repr__(self):
        return str(self)

    def interpret(self, valuation):
        pass

    def get_all_variables(self):
        return set()

    def is_valid(self):
        variables = list(self.get_all_variables())
        for valuation in all_valuations(variables):
            if self.interpret(valuation) == False:
                return (False, valuation)
        return (True, None)

    def is_satisfiable(self):
        variables = list(self.get_all_variables())
        for valuation in all_valuations(variables):
            if self.interpret(valuation) == True:
                return (True, valuation)
        return (False, None)

    def is_contradiction(self):
        variables = list(self.get_all_variables())
        for valuation in all_valuations(variables):
            if self.interpret(valuation) == True:
                return (False, valuation)
        return (True, None)

    def is_falsifiable(self):
        variables = list(self.get_all_variables())
        for valuation in all_valuations(variables):
            if self.interpret(valuation) == False:
                return (True, valuation)
        return (False, None)

    def all_true_interpreted_valuations(self):
        result = []
        variables = list(self.get_all_variables())
        for valuation in all_valuations(variables):
            if self.interpret(valuation) == True:
                result.append(valuation)
        return result


class Const(Formula):

    def __init__(self, value: bool):
        super(Const, self).__init__()
        self.value = value

    def interpret(self, valuation):
        return self.value

    def __str__(self):
        return f'({self.value})'


class Var(Formula):

    def __init__(self, p: str):
        super(Var, self).__init__()
        self.p = p

    def interpret(self, valuation):
        return valuation[self.p]

    def get_all_variables(self):
        return set([self.p])

    def __str__(self):
        return f'({self.p})'


class Not(Formula):

    def __init__(self, A: Formula):
        super(Not, self).__init__()
        self.A = A

    def interpret(self, valuation):
        return not self.A.interpret(valuation)

    def get_all_variables(self):
        return self.A.get_all_variables()

    def __str__(self):
        return f'~({self.A})'


class And(Formula):

    def __init__(self, A: Formula, B: Formula):
        super(And, self).__init__()
        self.A, self.B = A, B

    def interpret(self, valuation):
        return self.A.interpret(valuation) and self.B.interpret(valuation)

    def get_all_variables(self):
        return set.union(self.A.get_all_variables(), self.B.get_all_variables())

    def __str__(self):
        return f'({self.A} & {self.B})'


class Or(Formula):

    def __init__(self, A: Formula, B: Formula):
        super(Or, self).__init__()
        self.A, self.B = A, B

    def interpret(self, valuation):
        return self.A.interpret(valuation) or self.B.interpret(valuation)

    def get_all_variables(self):
        return set.union(self.A.get_all_variables(), self.B.get_all_variables())

    def __str__(self):
        return f'({self.A} | {self.B})'


class Impl(Formula):

    def __init__(self, A: Formula, B: Formula):
        super(Impl, self).__init__()
        self.A, self.B = A, B

    def interpret(self, valuation):
        # A => B = !A v B
        return not self.A.interpret(valuation) or self.B.interpret(valuation)

    def get_all_variables(self):
        return set.union(self.A.get_all_variables(), self.B.get_all_variables())

    def __str__(self):
        return f'({self.A} => {self.B})'


class Eq(Formula):

    def __init__(self, A: Formula, B: Formula):
        super(Eq, self).__init__()
        self.A, self.B = A, B

    def interpret(self, valuation):
        return self.A.interpret(valuation) == self.B.interpret(valuation)

    def get_all_variables(self):
        return set.union(self.A.get_all_variables(), self.B.get_all_variables())

    def __str__(self):
        return f'({self.A} <=> {self.B})'


def all_valuations(variables):
    for k in range(len(variables) + 1):
        for true_variables in combinations(variables, k):
            valuation = {var: False for var in variables}
            valuation.update({var: True for var in true_variables})
            yield valuation


def vars(names):
    return [Var(name.strip()) for name in names.split(',')]




class CNF(object):
    def __init__(self):
        super(CNF, self).__init__()
        self.clauses = []
        self.number_to_var_name = {}
        self.var_name_to_number = {}

    def add_clause(self, clause):
        for literal in clause:
            var_name = literal.strip('-')
            if var_name not in self.var_name_to_number:
                var_number = len(self.var_name_to_number) + 1
                self.var_name_to_number[var_name] = var_number
                self.number_to_var_name[var_number] = var_name
        self.clauses.append(clause)

    def dimacs(self):
        result = f'p cnf {len(self.var_name_to_number)} {len(self.clauses)}\n'
        for clause in self.clauses:
            for literal in clause:
                var_name = literal.strip('-')
                if literal[0] == '-':
                    result += '-'
                result += f'{self.var_name_to_number[var_name]} '
            result += '0\n'
        return result





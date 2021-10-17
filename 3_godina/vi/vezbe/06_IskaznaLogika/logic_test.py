import logic


def test():
    x, y, z = logic.vars('x, y, z');
    valuation = {'x': True, 'y': False, 'z': False}
    formula = (x & y) | ~z
    print(f'Formula: {formula}')
    print(f'Valuation: {valuation}')
    print(f'Variables in formula: {formula.get_all_variables()}')
    print(f'Interpretation of formula for valuation is {formula.interpret(valuation)}')
    print(f'Validity of formula: {formula.is_valid()}')
    print(f'Satisfiability of formula: {formula.is_satisfiable()}')
    print(f'Contradictory of formula: {formula.is_contradiction()}')
    print(f'Falsifiability of formula: {formula.is_falsifiable()}')
    print(f'All true interpreted valuations of formula: {formula.all_true_interpreted_valuations()}')


def test_tautology():
    x, y = logic.vars('x, y')
    valuation = {'x': True}
    formula = x | ~x
    print(f'Formula: {formula}')
    print(f'Valuation: {valuation}')
    print(f'Variables in formula: {formula.get_all_variables()}')
    print(f'Interpretation of formula for valuation is {formula.interpret(valuation)}')
    print(f'Validity of formula: {formula.is_valid()}')
    print(f'Satisfiability of formula: {formula.is_satisfiable()}')
    print(f'Contradictory of formula: {formula.is_contradiction()}')
    print(f'Falsifiability of formula: {formula.is_falsifiable()}')
    print(f'All true interpreted valuations of formula: {formula.all_true_interpreted_valuations()}')


def test_minesweepers():
    # Neka je data sledeca konfiguracija:
    # |1|A|C|
    # |1|B|2|
    # Naci pozicije gde je mina?
    print('Minesweeper konfiguracija:')
    print('|1|A|C|')
    print('|1|B|2|')

    A, B, C = logic.vars('A, B, C')
    formula = (A | B) & ~(A & B) & \
              (B | A) & ~(B & A) & \
              ((A & B & ~C) | (A & ~B & C) | (~A & B & C))

    print(f'Resenje: {formula.all_true_interpreted_valuations()}')


def test_boxes():
    print('Date su dve kutije A, i B. Robot mora da ubaci u jednu kutuju dati objekat.')

    A, B = logic.vars('A, B')
    formula = (A | B) & ~(A & B) & ~(~A & ~B)

    print(f'Resenje: {formula.all_true_interpreted_valuations()}')


def test_coin():
    print('Neka je data tabla dimenzije 2x2:')
    print('|A|B|')
    print('|C|D|')
    print('Tacno jedan zeton mozemo postaviti u jednom redu')

    A, B, C, D = logic.vars('A, B, C, D')
    formula = (A | B) & (C | D) & ~(A & B) & ~(C & D)

    print(f'Resenje: {formula.all_true_interpreted_valuations()}')


def test_bits():
    print('Bitovi 3-bitnog polja moraju biti jednaki')

    A, B, C = logic.vars('A, B, C')
    formula = (A == B) & (A == C) & (B == C)

    print(f'Resenje: {formula.all_true_interpreted_valuations()}')


def test_bits2():
    print('Dva 2-bitna broja se sabiraju i daju 3')
    # A B
    # C D
    # ---
    # 1 1 = 3

    A, B, C, D = logic.vars('A, B, C, D')
    formula = (B | D) & ~(B & D) & (A | C) & ~(A & C)

    print(f'Resenje: {formula.all_true_interpreted_valuations()}')


def test_bin_palindrom():
    print('4-bitni broj ABCD koji je palindrom i cije cifre nisu jednake:')

    A, B, C, D = logic.vars('A, B, C, D')
    formula = (A == D) & (B == C) & (A | B) & ~(A == B & B == C & C == D)

    print(f'Resenje: {formula.all_true_interpreted_valuations()}')


def test_crveno_crno():
    print('Tri polja ABC se boje crveno ili crno')
    print('Ako je prvo polje obojeno crveno onda druga dva moraju biti iste boje')
    print('Ako je drugo polje obojeno crveno onda trece mora biti crno')

    A, B, C = logic.vars('A, B, C')
    formula = (A >> (B == C)) & (B >> ~C)

    print(f'Resenje: {formula.all_true_interpreted_valuations()}')


def test_bojenje_trougla():
    print('Obojiti temena trougla A, B, C sa dve boje tako da nikoja nisu obojena istom bojom')
    print('     A       ')
    print('    / \      ')
    print('   /   \     ')
    print('  B-----C    ')

    A, B, C = logic.vars('A, B, C')
    formula = ~(A == B) & ~(B == C) & ~(C == A)

    print(f'Resenje: {formula.all_true_interpreted_valuations()}')


def test_crveno_crno_tabela():
    print('Treba obojiti polja tabele crveno ili crno:')
    print('|A|B|')
    print('|C|D|')
    print('Ako je polje A obojeno crveno, onda barem jedno od ostalih mora biti crno')
    print('Ako je polje D obojeno crno, onda barem dva ostala moraju buti crvena')

    A, B, C, D = logic.vars('A, B, C, D')
    formula = (A >> (~B | ~C | ~D)) & (~D >> ((A & D) | (B & C) & (A & C)))

    print(f'Resenje: {formula.all_true_interpreted_valuations()}')


if __name__ == '__main__':
    print('---------------------------------------------')
    test()
    print('---------------------------------------------')
    test_tautology()
    print('---------------------------------------------')
    test_minesweepers()
    print('---------------------------------------------')
    test_boxes()
    print('---------------------------------------------')
    test_coin()
    print('---------------------------------------------')
    test_bits()
    print('---------------------------------------------')
    test_bits2()
    print('---------------------------------------------')
    test_bin_palindrom()
    print('---------------------------------------------')
    test_crveno_crno()
    print('---------------------------------------------')
    test_bojenje_trougla()
    print('---------------------------------------------')
    test_crveno_crno_tabela()
    print('---------------------------------------------')




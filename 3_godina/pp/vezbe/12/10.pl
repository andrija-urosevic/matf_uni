% Liste

% sadrzi(e, l) <- da li je element e unutar liste l?
sadrzi(X, [X|_]) :- !.
sadrzi(X, [G|R]) :- X \== G, sadrzi(X, R).

% duzina(l, n) <- da li je lista l duzine n?
duzina([], 0).
duzina([_|R], N) :- duzina(R, N1), N is N1 + 1.

% suma(l, s) <- da li je suma list l vrednost s?
suma([], 0).
suma([G|R], S) :- number(G), suma(R, S1), S is S1 + G.

% arsr(l, a) <- da li je aritmeticka sredina od liste l jednaka vednosti s?
arsr([], 0) :- !.
arsr(L, A) :- duzina(L, N), N > 0, suma(L, S), A is S / N.

% ucitaj(n, l) -> ucitava listu l duzine n.
ucitaj(N, _) :- N < 0, !.
ucitaj(0, []).
ucitaj(N, [G|R]) :- N > 0, 
                    write("unesite element "), read(G), nl, 
                    M is N - 1,
                    ucitaj(M, R).

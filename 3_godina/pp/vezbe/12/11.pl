% dodajPocetak(x, l, nl) <- da li je nl: [x|l]
dodajPocetak(X, L, [X|L]).

% dodajKraj(x, l, nl) <- da li je nl: l++x
dodajKraj(X, [], [X]).
dodajKraj(X, [G|R], [G|R1]) :- dodajKraj(X,R,R1).

% obrisiPrvi(l, nl) <- nl je lista l bez pocetnog elementa.
obrisiPrvi([_|R], R).

% obrisiPoslednji(l, nl) <- nl je lista l bez poslednjeg elementa.
obrisiPoslednji([_], []) :- !.
obrisiPoslednji([G|R], [G|R1]) :- obrisiPoslednji(R, R1).

% obrisi(x, l, nl) <- da li je lista nl lista l bez elementa x?
obrisi(_, [], []) :- !.
obrisi(X, [X|R], R1) :- obrisi(X, R, R1), !.
obrisi(X, [G|R], [G|R1]) :- X \== G, obrisi(X, R, R1).

% obrisiPrvo(x, l, nl) <- da li je lista nl lista l bez prvog
% pojavljivanja elementa x?
obrisiPrvo(_, [], []) :- !.
obrisiPrvo(X, [X|R], R) :- !.
obrisiPrvo(X, [G|R], [G|R1]) :- X \== G, obrisiPrvo(X, R, R1).

% obrisiK(l, k, nl) <- da li je lista nl lista l bez k-tog elemnta?
obrisiK([_|R], 1, R) :- !.
obrisiK([G|R], K, [G|R1]) :- K1 is K - 1, obrisiK(R, K1, R1).

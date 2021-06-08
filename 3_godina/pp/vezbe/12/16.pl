% maxEl(L, X) <- da li je X maksimalni element liste?
maxEl([X], X).
maxEl([G|R], X) :- maxEl(R, Y), G < Y, X is Y, !.
maxEl([G|R], X) :- maxEl(R, Y), G >= Y, X is G.

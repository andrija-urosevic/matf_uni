% par(muskarac, muskaracMaska, zena, zenaMaska)

parovi(L) :-
    L = [par(_,_,_,_),
         par(_,_,_,_),
         par(_,_,_,_),
         par(_,_,_,_)],
    clan(par(marko,_,_,macka), L),
    pre(par(vasa,_,_,_), par(_,princ,_,_), L),
    pre(par(laza,_,_,_), par(_,_,marija,_), L),
    pre(par(_,_,marija,_), par(_,_,bojana,_), L),
    pre(par(_,_,ivana,_), par(_,_,_,snezana), L),
    clan(par(pera,paja_patak,Z,vestica), L), Z \= bojana,
    pre(par(_,U,_,ciganka), par(_,U,ana,_), L), U \= betmen,
    clan(par(_,medved,_,_), L),
    pre(par(X,_,_,_), par(marko,_,_,_), L),
    pre(par(Y,_,_,_), par(marko,_,_,_), L), X \= Y, X \= marko,
    pre(par(_,_,_,_), par(vasa,_,_,_), L).

clan(X, [X|_]).
clan(X, [_|R]) :- clan(X, R).

pre(X, Y, [X|R]) :- clan(Y, R).
pre(X, Y, [_|R]) :- pre(X, Y, R).


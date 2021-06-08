% poredica(majka, cerka, prezime)

porodice(L) :-
    L = [porodica(lenka,petra,_),
         porodica(_,_,_),
         porodica(_,_,_),
         porodica(_,_,_)],
    clan(porodica(petra,_,_), L),
    clan(porodica(milica,_,_), L),
    clan(porodica(lenka,_,_), L),
    clan(porodica(jovana,_,_), L),
    clan(porodica(_,petra,_), L),
    clan(porodica(_,milica,_), L),
    clan(porodica(_,lenka,_), L),
    clan(porodica(_,jovana,_), L),
    clan(porodica(_,_,peric), L),
    clan(porodica(_,_,mikic), L),
    clan(porodica(_,_,lazic), L),
    clan(porodica(_,_,jovic), L),
    clan(porodica(A1,_,_), L), clan(porodica(A2,_,_), L), A1 \= A2,
    clan(porodica(_,B1,_), L), clan(porodica(_,B2,_), L), B1 \= B2,
    clan(porodica(_,_,C1), L), clan(porodica(_,_,C2), L), C1 \= C2,
    not(clan(porodica(petra,_,peric), L)),
    not(clan(porodica(milica,_,mikic), L)),
    not(clan(porodica(lenka,_,lazic), L)),
    not(clan(porodica(jovana,_,jovic), L)),
    not(clan(porodica(_,petra,peric), L)),
    not(clan(porodica(_,milica,mikic), L)),
    not(clan(porodica(_,lenka,lazic), L)),
    not(clan(porodica(_,jovana,jovic), L)),
    clan(porodica(X,_,peric), L), clan(porodica(milica,X,_), L),
    not(clan(porodica(Y,Y,_), L)).

clan(X, [X|_]).
clan(X, [_|R]) :- clan(X, R).



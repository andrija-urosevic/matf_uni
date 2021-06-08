% dete(ime, prezime, godine)

deca(L) :- 
    L = [dete(lazar,jankovic,_),
         dete(_,_,_),
         dete(_,_,_),
         dete(_,_,_),
         dete(_,_,_)],
    clan(dete(kata,_,_), L),
    clan(dete(lazar,_,_), L),
    clan(dete(marko,_,_), L),
    clan(dete(nevenka,_,_), L),
    clan(dete(ognjen,_,_), L),
    clan(dete(_,filipovic,_), L),
    clan(dete(_,grbovic,_), L),
    clan(dete(_,ivanovic,_), L),
    clan(dete(_,jankovic,_), L),
    clan(dete(_,hadzic,_), L),
    clan(dete(_,_,2), L),
    clan(dete(_,_,3), L),
    clan(dete(_,_,4), L),
    clan(dete(_,_,5), L),
    clan(dete(_,_,6), L),
    clan(dete(_,ivanovic,X), L), X1 is X + 1, clan(dete(kata,_,X1), L),
    clan(dete(marko,_,Y), L), Y1 is Y + 3, clan(dete(_,filipovic,Y1), L),
    clan(dete(_,hadzic,Z), L), Z1 is 2*Z, clan(dete(ognjen,_,Z1), L).

clan(X, [X|_]).
clan(X, [_|R]) :- clan(X, R).



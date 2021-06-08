% duplikati(L, L1), unija(L1, L2, L), preske(L1, L2, L), razlika(L1, L2, L).

sadrzi(X, [X|_]) :- !.
sadrzi(X, [G|R]) :- G =\= X, sadrzi(X, R).

duplikati([], []).
duplikati([G|R], [G|R1]) :- not(sadrzi(G, R)), duplikati(R, R1), !.
duplikati([_|R], R1) :- duplikati(R, R1).

spoji([], L, L).
spoji([G|R1], L, [G|R2]) :- spoji(R1, L, R2).

unija(L1, L2, L) :- spoji(L1, L2, L3), duplikati(L3, L).

presek([], _, []).
presek([G|R1], L2, [G|R3]) :- sadrzi(G, L2), presek(R1, L2, LP), duplikati(LP, R3), !.
presek([_|R1], L2, L) :- presek(R1, L2, LP), duplikati(LP, L).

razlika([], _, []).
razlika([G1|R1], L2, R3) :- sadrzi(G1, L2), razlika(R1, L2, LP), duplikati(LP, R3), !.
razlika([G|R1], L2, [G|R3]) :- razlika(R1, L2, R3).

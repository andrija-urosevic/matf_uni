% n queens 
:- use_module(library(aggregate)).

queens(Qs, N) :- length(Qs, N),
                 Qs ins 1..N,
                 safeQueens(Qs),
                 label(Qs).

safeQueens([]).
safeQueens([Q|Qs]) :- safeQueens(Qs, Q, 1), safeQueens(Qs).

safeQueens([], _, _).
safeQueens([Q|Qs], Q0, D0) :- Q0 #\= Q,
                              abs(Q - Q0) #\= D0,
                              D1 #= D0 + 1,
                              safeQueens(Qs, Q0, D1).


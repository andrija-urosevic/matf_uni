% izbaci3(N, X) <- da li je broj X, broj N bez cifre 3?
izbaci3(3, 0) :- !.
izbaci3(N, N) :- N < 10.
izbaci3(N, X) :- N >= 10, N1 is N div 10, O is N mod 10,
                 O =:= 3, izbaci3(N1, X1), X is X1, !.
izbaci3(N, X) :- N >= 10, N1 is N div 10, O is N mod 10,
                 O =\= 3, izbaci3(N1, X1), X is 10*X1 + O.

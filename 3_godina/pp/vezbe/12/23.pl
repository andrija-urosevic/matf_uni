% sortirana(L) <- da li je L sortirana?

sortirana([]) :- !.
sortirana([_]) :- !.
sortirana([X,Y|R]) :- X =< Y, sortirana(R).


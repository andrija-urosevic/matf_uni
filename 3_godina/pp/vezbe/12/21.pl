% interval(X, Y, L) <- Da li je lista L interval [X,..,Y]?
interval(Y, Y, [Y]) :- !.
interval(X, Y, [X|R]) :- X1 is X + 1, interval(X1, Y, R).

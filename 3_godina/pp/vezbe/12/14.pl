% zameni(X, Y, L, NL) <- da li je NL lista koja sadrzi elemente 
% liste L tako da je svako X zamenjeno sa Y
zameni(_, _, [], []).
zameni(X, Y, [X|R], [Y|R1]) :- zameni(X, Y, R, R1), !.
zameni(X, Y, [G|R], [G|R1]) :- X \== G, zameni(X, Y, R, R1).

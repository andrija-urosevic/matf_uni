uni(X, Y) :- X = Y.

eql(X, Y) :- X == Y.

abs(X, X) :- X >= 0, !.
abs(X, AX) :- AX is -X.



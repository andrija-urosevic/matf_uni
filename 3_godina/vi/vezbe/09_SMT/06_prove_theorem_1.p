% Dve nemimoilazne prave se seku ili su paralelene.
% Prave koje se seku leže u istoj ravni.
% Prave koje su paralelene leže u istoj ravni.
% Dve nemimoilazne prave leže u istoj ravni.


fof(a1, axiom, ![X,Y]:(~m(X,Y) => (s(X,Y) | p(X,Y)))).
fof(a2, axiom, ![X,Y]:(s(X,Y) => r(X,Y))).
fof(a3, axiom, ![X,Y]:(p(X,Y) => r(X,Y))).

fof(c, conjecture, ![X,Y]:(~m(X,Y) => r(X,Y))).



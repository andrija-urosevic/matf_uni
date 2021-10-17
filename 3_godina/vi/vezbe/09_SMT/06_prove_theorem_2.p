% Svaka dva brata imaju zajedničkog roditelja.
% Roditelj je stariji od deteta.
% Postoje braća.
% Ni jedna osoba nije starija od druge.

fof(a1, axiom, ![X,Y]: (?[Z]: (b(X,Y) => (r(Z,X) & r(Z,Y))))).
fof(a2, axiom, ![X,Y]: (r(X,Y) => s(X,Y))).
fof(a3, axiom, ?[X,Y]: (b(X,Y))).
fof(c1, conjecture, ![X,Y]: (~s(X,Y))).




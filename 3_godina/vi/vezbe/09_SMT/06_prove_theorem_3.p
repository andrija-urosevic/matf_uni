% Ako postoji cipela koja u svakom trenutku odgovara svakoj nozi,
% onda za svaku nogu postoji cipela koja joj u nekom trenutku
% odgovara i za svaku nogu postoji trenutak takav da postoji cipela
% koja joj u tom trenutku odgovara.

fof(a, axiom, ?[X]: (![Y,Z]: p(X,Y,Z))).
fof(c, conjecture, (![Y]: (?[X,Z]: p(X,Y,Z))) & (![Y]: (?[Z,X]: p(X,Y,Z)))).



% Hello, world! Komentar

veci(slon, konj).
veci(konj, magarac).
veci(magarac, pas).

je_veci(X, Y) :- veci(X, Y).
je_veci(X, Y) :- veci(X, Z), je_veci(Z, Y).

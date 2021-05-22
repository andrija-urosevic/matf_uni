musko(mihajlo).
musko(stevan).
musko(petar).
musko(mladen).
musko(rajko).

zensko(milena).
zensko(milica).
zensko(jelena).
zensko(senka).
zensko(mina).
zensko(maja).

roditelj(mihajlo, milica).
roditelj(mihajlo, senka).
roditelj(milena, rajko).
roditelj(maja, petar).
roditelj(maja, mina).
roditelj(stevan, mladen).
roditelj(stevan, jelena).
roditelj(milica, mladen).
roditelj(milica, jelena).


% X je majka od Y
majka(X, Y) :- zensko(X), roditelj(X, Y).

% X je otac od Y
otac(X, Y) :- musko(X), roditelj(X, Y).

% X je brat od Y
brat(X, Y) :- musko(X), roditelj(Z, X), roditelj(Z, Y), X \== Y.
sestra(X, Y) :- zensko(X), roditelj(Z, X), roditelj(Z, Y), X \== Y.

% X je ujak od Y
ukaj(X, Y) :- brat(Z, X), roditelj(Z, Y).
tetka(X, Y) :- sestra(Z, X), roditelj(Z, Y).

predak(X, Y) :- roditelj(X, Y).
predak(X, Y) :- roditelj(X, Z), predak(Z, Y).


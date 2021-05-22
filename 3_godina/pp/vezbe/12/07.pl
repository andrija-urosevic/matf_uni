% sumaCifara(N, SC) <- N broj, SC suma cifara broja N
sumaCifara(N, SC) :- N < 0, 
                     N1 is -N, 
                     sumaCifara(N1, SC), !.
sumaCifara(N, N) :- N < 10, !.
sumaCifara(N, SC) :- N >= 10, 
                     N1 is (N // 10), 
                     C is (N mod 10), 
                     sumaCifara(N1, SC1), 
                     SC is SC1 + C.

brojCifara(N, BC) :- N < 0, 
                     N1 is -N,
                     brojCifara(N1, BC), !.
brojCifara(N, 1) :- N < 10, !.
brojCifara(N, BC) :- N >= 10, 
                     N1 is (N // 10), 
                     brojCifara(N1, BC1), 
                     BC is BC1 + 1.

maksimum(A, B, A) :- A >= B, !.
maksimum(_, B, B).

maxCifra(N, MC) :- N < 0,
                   N1 is -N,
                   maxCifra(N1, MC), !.
maxCifra(N, N) :- N < 10, !.
maxCifra(N, MC) :- N >= 10,
                   N1 is (N // 10),
                   C is (N mod 10),
                   maxCifra(N1, MC1),
                   maksimum(MC1, C, MC).

sumaKvadrata(1, 1) :- !.
sumaKvadrata(N, SK) :- N > 1,
                       N1 is N - 1,
                       sumaKvadrata(N1, SK1),
                       SK is SK1 + N * N.

faktorijel(1, 1) :- !.
faktorijel(N, F) :- N > 1,
                    N1 is N - 1,
                    faktorijel(N1, F1),
                    F is F1 * N.

deli(D1, X, D1) :- X mod D1 =:= 0, !.
deli(_, _, 0).

sumaDel(_, 1, 1) :- !.
sumaDel(X, D, S) :- D > 1,
                    D1 is D - 1, 
                    sumaDel(X, D1, S1),
                    deli(D, X, K),
                    S is S1 + K.

sumaDelioca(X, S) :- sumaDel(X, X, S).

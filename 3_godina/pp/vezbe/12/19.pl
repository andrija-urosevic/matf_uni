% podeli(L, N, L1, L2) <- L1 + L2 su L, gde je L1 duzine N.
podeli(L, N, [], L) :- N =< 0, !.
podeli([G|R], N, [G|R1], L2) :- N > 0, N1 is N - 1, podeli(R, N1, R1, L2).


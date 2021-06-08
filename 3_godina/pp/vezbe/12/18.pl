% parNepar(L, L1, L2) <- lista L1 sadrzi sve parne elemente liste L, % dok lista L2 sadrzi sve neparne elemente liste L?
parNepar([], [], []).
parNepar([G|R], [G|R1], L2) :- G mod 2 =:= 0, parNepar(R, R1, L2), !.
parNepar([G|R], L1, [G|R2]) :- G mod 2 =\= 0, parNepar(R, L1, R2).

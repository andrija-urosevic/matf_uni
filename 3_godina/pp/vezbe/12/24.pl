% spoji(L1, L2, L) <- merge(L1, L2) == L?
spoji([], L, L).
spoji(L, [], L).
spoji([G1|R1], [G2|R2], [G1|R3]) :- G1 < G2, spoji(R1, [G2|R2], R3), !.
spoji([G1|R1], [G2|R2], [G2|R3]) :- G2 =< G1, spoji([G1|R1], R2, R3).



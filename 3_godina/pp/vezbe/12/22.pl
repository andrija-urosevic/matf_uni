% skalar(V1, V2, S) <- Skalarni proizvod vektora V1 i V2 je S.
skalar([], [], 0) :- !.
skalar([G1|R1], [G2|R2], S) :- skalar(R1, R2, S1), S is S1 + G1 * G2.

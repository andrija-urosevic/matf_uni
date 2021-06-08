% podeli(l, l1, l2) <- lista l deli se na l1 i l2, gde l1 sadrzi
% pozitivne dok l2 sadrzi negativne elemente
podeli([], [], []).
podeli([G|R], [G|R1], L2) :- G >= 0, podeli(R, R1, L2), !.
podeli([G|R], L1, [G|R2]) :- G < 0, podeli(R, L1, R2).

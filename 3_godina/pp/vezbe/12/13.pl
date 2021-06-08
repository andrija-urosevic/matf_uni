% dupliraj(l, nl) nl je lista l koja sadrzi pozitivne elemente liste l duplo.
dupliraj([], []).
dupliraj([G|R], [G,G|R1]) :- G > 0, dupliraj(R, R1), !.
dupliraj([G|R], [G|R1]) :- G =< 0, dupliraj(R, R1).

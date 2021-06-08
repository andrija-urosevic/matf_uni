% insetionSort
insertionSort([], []) :- !.
insertionSort([G|R], SL) :- insertionSort(R, SL1), insert(G, SL1, SL).

insert(X, [], [X]) :- !.
insert(X, [G|R], [X, G|R]) :- X =< G, !.
insert(X, [G|R], [G|SL]) :- insert(X, R, SL).

% mergeSort
mergeSort([], []) :- !.
mergeSort([X], [X]) :- !.
mergeSort(N, NN) :- devide(N, L, R),
                    mergeSort(L, NL),
                    mergeSort(R, NR),
                    merge(NL, NR, NN).

devide([], [], []) :- !.
devide([X], [X], []) :- !.
devide([G1, G2|R1], [G1|L], [G2|R]) :- devide(R1, L, R).

merge(L, [], L) :- !.
merge([], R, R) :- !.
merge([GL|RL], [GR|RR], [GL|R]) :- GL < GR, merge(RL, [GR|RR], R), !.
merge([GL|RL], [GR|RR], [GR|R]) :- GL >= GR, merge([GL|RL], RR, R).


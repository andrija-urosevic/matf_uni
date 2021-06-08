% savrsen(N) <- da li je N savrsen broj?
% da li je N jednak sumi svojih pravih delilaca.

sumaDelioca(N, S) :- sumaDeliocaPom(N, S, 1).

sumaDeliocaPom(N, 0, I) :- I >= N // 2.
sumaDeliocaPom(N, S, I) :- I =< N // 2, N mod I =:= 0, 
    I1 is I + 1, sumaDeliocaPom(N, S1, I1), S is S1 + I.
sumaDeliocaPom(N, S, I) :- I =< N // 2, N mod I =\= 0, 
    I1 is I + 1, sumaDeliocaPom(N, S1, I1), S is S1.

savrsen(N) :- sumaDelioca(N, S), N =:= S.

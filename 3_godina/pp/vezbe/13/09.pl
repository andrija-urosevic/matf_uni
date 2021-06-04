% Pekara Kiflica: H i K
% Mesenje: H = 10min, K = 12min
% Brasno: H = 300g, K = 120g
% Zarada: H = 7din, K = 9din
% Ukupno vreme: 20h=1200min
% Ukupno brasna: 20kg=20000g

kiflica(Vs) :- Vs = [H, K],
               Vs ins 0..1000,
               10*H + 12*K #=< 1200,
               300*H + 120*K #=< 20000,
               labeling([max(7*H + 9*K)], Vs),
               Z #= 7*H + 9*K,
               write('Zarada je '), write(Z), nl.

% Start: 250 radnika
% Budzet: 26000e
% Projekat sati mesecno: 51200
% Cena kursta: E = 100e, D = 105e
% Dobit projekat sata: E = 150, D = 170
% Dobit po projekat satu: E = 5e, D = 6e

uslov(Vs) :- Vs = [E, D],
             Vs ins 0..250,
             E + D #= 250,
             150*E + 170*D #=< 51200,
             100*E + 105*D #=< 26000,
             labeling([max(5*150*E + 6*170*D - (100*E + 105*D))], Vs),
             Z #= 5*150*E + 6*170*D - (100*E + 105*D),
             write('Zarada: '), write(Z), nl.

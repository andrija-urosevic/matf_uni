% ===================================================================
% Bojenje grafa
% Posmatra se karta i na njoj Srbija i njeni susedi.
% Potrebno je naci bojenje karte takvo da svaka zemlja bude obojena zutom, zelenom ili plavom bojom,
% a da susedne zemlje budu obojene razlicitim bojama.  
% ===================================================================

boja(zuta).
boja(plava).
boja(zelena).
boja(crna).

bojanje(Srb, Cg, Mak, Bug, Rum, Madj, Hrv, BiH) :-
    sused(Srb, Cg),
    sused(Srb, Mak),
    sused(Srb, Bug),
    sused(Srb, Rum),
    sused(Srb, Madj),
    sused(Srb, Hrv),
    sused(Srb, BiH),
    sused(Cg, BiH),
    sused(Cg, Hrv),
    sused(BiH, Hrv),
    sused(Hrv, Madj),
    sused(Madj, Rum),
    sused(Rum, Bug).

sused(X, Y) :- boja(X), boja(Y), X \== Y.


% ===================================================================
% Logicki zadatak (zapisati tvrdjenja, otkriti ko je udario macku)
%
% Ko je udario macku Tunu?
% Macka je zivotinja.
% Vlasnik psa voli zivotinje.
% Janko ima psa. Marko nema psa.
% Ne bi udario zivotinju ko voli zivotinje.
% Macku bi udario onaj koji bi je mozda udario i nije da je ne bi udario.
% ===================================================================

macka(tuna).
vlasnikpsa(janko).
mozda_udario(marko, tuna).
mozda_udario(janko, tuna).

zivotinja(X) :- macka(X).
voli_zivotinje(X) :- vlasnikpsa(X).
ne_bi_udario(X, Y) :- voli_zivotinje(X), zivotinja(Y).
uradio(X, Y) :- mozda_udario(X, Y), \+(ne_bi_udario(X, Y)).


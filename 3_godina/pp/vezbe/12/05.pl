% prestupna godina:
% 1. deljiva sa 4 ali nije sa 100
% 2. deljiva sa 400
prestupna(X) :- X mod 4 =:= 0, X mod 100 =\= 0, !.
prestupna(X) :- X mod 400 =:= 0.

% broj dana u mesecu:
% 31 - jan, mar, maj, jul, avg, okt, dec
% 30 - apr, jun, sep, nov
% 28/29 - feb
brdana(jan, _, 31).
brdana(feb, X, 28) :- not(prestupna(X)), !.
brdana(feb, X, 29) :- prestupna(X).
brdana(mar, _, 31).
brdana(apr, _, 30).
brdana(maj, _, 31).
brdana(jun, _, 30).
brdana(jul, _, 31).
brdana(avg, _, 31).
brdana(sep, _, 30).
brdana(okt, _, 31).
brdana(nov, _, 30).
brdana(dec, _, 31).


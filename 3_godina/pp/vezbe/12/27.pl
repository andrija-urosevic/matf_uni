% automobil, vlasnik, sifra???

automobil(123, audi).
automobil(223, bmw).
automobil(321, tesla).

vlasnik(pera, 123).
vlasnik(marko, 223).
vlasnik(mira, 321).

brziSifra(123, 223).
brziSifra(231, 223).

brziNaziv(X, Y) :- 
    automobil(S1, X), 
    automobil(S2, Y), 
    brziSifra(S1, S2).

imaAutomobil(X) :- vlasnik(X, _).

imaBrzi(X, Y) :- 
    vlasnik(X, S1), vlasnik(Y, S2),
    brziSifra(S1, S2).

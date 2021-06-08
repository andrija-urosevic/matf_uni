% poClanu(Porodica, Prosek) <- racuna prosek po clanu porodice?
%
stan(peric, 100).
stan(matic, 80).
stan(maric, 70).

clan(peric, 4).
clan(matic, 3).
clan(maric, 4).

poClanu(Porodica, Prosek) :- 
    stan(Porodica, KvadraturaStana),
    clan(Porodica, BrojClanova),
    Prosek is KvadraturaStana / BrojClanova.

# Haskel

## Uvod

* Haskel je *cisto funkcionalan programski jezik*.
* Za razliku od imperativnih programskih jezika u kojima navodimo
  sekvencu naredbi u cisto funkcionalnim programskim jezicima
  navodimo sta su stvari.
* Na primer: 
    * Faktorijel nekog broja je proizvod sveh brojeve od 1 
      do tog broja.
    * Suma liste brojeva je prvi broj liste plus suma ostalih brojeva
      liste.
* Ovo se iskazuje preko funkcija.
* Funkcije nemaju bocne-efekte. Ako je funkcija pozvana dva puta za
  iste parametre, onda je garantovana da vrati isti rezultat 
  (referencijalna transparentnost).
* Haskel je *lenj*.
* Haskel nece izvrsiti funkcije dok nije forsiran da pokaze rezultat.
* Zbog toga je haskel program *serija transformacije nad podacima*.
* Omogucava beskonacne strukture podataka.
  * Za listu `xs` imamo funkciju `doubleMe` koja mnozi
    svaki element liste sa 2. Funkcija
    `doubleMe(doubleMe(doubleMe(xs)))` koja mnozi svaki element liste
    sa 8, a zbog lenjosti se prolazi kroz listu samo jednom.
* Haskel je *strogo tipiziran*. 
  * U svakom trenutku kompajliranja, kompajler zna koji deo koda je
    broj, a koji je string, itd.
* Haskel za ovo koristi sistem koji ima *zakljucivanje tipova*.
  * Ne mora se svaki deo koda eksplicitno oznaciti nekim tipom, ako to haskel
    moze inteligentno zakljuciti. `a = 5 + 4` bice tipa `Number`.
* Haskel je *elegantan i koncizan*.
    
## Pocetak

### GHCI

* Pokretanje ghc's interaktivnog moda: `ghci`.
* Jednostavne aritmeticke operacije:
```haskell
Prelude> 2 + 15
17
Prelude> 49 * 100
4900
Prelude> 1892 - 1472
420
Prelude> 5 / 2
2.5
```
* Jednostavne bulove operacije:
```haskell
Prelude> True && False
False
Prelude> True && True
True
Prelude> False || True
True
Prelude> not False
True
Prelude> not (True && True)
False
```
* Testiranje jednakosti:
```haskell
Prelude> 5 == 5
True
Prelude> 1 == 0
False
Prelude> 5 /= 5
False
Prelude> 5 /= 4
True
Prelude> "hello" == "hello"
True
```
* Do sada smo koristili funkcije sve vreme. 
  * Na primer: `*` je funkcija koja uzima dva broja i mnozi ih.
  * Poziva se tako sto se nalazi izmedju dva parametra(broja), i 
    ova naziva *infiksnom funkcijom*. Ostale funkciju koje se
    ne koriste nad brojevima se nazivaju *prefiksne funkcije*.
* Prefiksne funkcije se pozivaju tako sto se navede ime funkcije i   
  parametri funkcije razdvojeni razmakom.
```haskell
Prelude> succ 8
9
Prelude> min 9 10
9
Prelude> min 3.4 4.2
3.4
Prelude> min 3 3.4
3.0
Prelude> max 100 101
101
Prelude> succ 9 * 10
100
Prelude> succ (9 * 10)
91
Prelude> div 92 10
9
Prelude> 92 `div` 10
9
```
* !Opasnost: 
  * `bar (bar 3)` nije poziv funkcije `bar` sa parametrima `bar` 
    i `3`, vec je poziv funkcija `bar` sa parametrom `bar 3`.

### Prva funkcija

## Tipovi i Tipovneklase

## Sintaska u Funkcijama



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

## Tipovi i Tipovneklase

## Sintaska u Funkcijama



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

### Tipovi

* Tipovi svakog izraza su poznati pri kompajliranju, tj. haskel ima staticni
  sistem tipova. Zbog ovog svojstva puno stvari su poznate za vreme 
  kompajliranja, sto omogucava vecu sigurnost programa.
* Haskel ima zakljucivanje tipova. Ako napisemo broj u haskelu, ne moramo 
  mu rece da je to broj, on to moze *zaljuciti* sam.
* Tip je labela koju svaki izraz ima, kazuje nam kojoj kategoriji taj 
  izraz pripada. 
* Svaki tip pocinje velikim slovom.
* Komanda `:t` nakon koje je bilo koji izraz, vraca taj izraz nakon koga se
  nalazi `::` (cita se *je tipa*) nakon cega je i sam tip izraza.
```haskell
Prelude> :t 'a'
'a' :: Char
Prelude> :t "a"
"a" :: [Char]
Prelude> :t True
True :: Bool
Prelude> :t (True, 'a')
(True, 'a') :: (Bool, Char)
Prelude> :t 4 == 5
4 == 5 :: Bool
```
* Funkcije takodje imaju tipove. Pri deklaraciji funkcije dobra je praksa,
  deklarisati tip te funkcije eksplicitno.
```haskell
removeLowerCase :: [Char] -> [Char]
removeLowerCase str = [ c | c <- str, not (elem c ['a'..'z']) ]
```
* Funkcija `removeLowerCase` je tipa `[Char] -> [Char]`, sto znaci da slika
  string u neki drugi string.
* Ako hocemo da imamo funkciju sa vise parametra onda to navodimo na 
  sledeci nacin:
```haskell
addThree :: Int -> Int -> Int -> Int
addThree x y z = x + y + z
```
* Ovde su tipovi parametra i povratni tip razdvojeni sa `->`. Zadnji tip je
  povratni tip, dok su ostali parametriski tipovi.
  * Razlog za ovo bice kasnije objasnjen.
*  Kako su funkcije takodje izrazi njihov tip moguce je takodje dobiti sa `:t`
* Neki cesti tipovi:
    1. `Int` - 32-bitni celi brojevi. Imaju ogranicenje.
    2. `Integer` - celi brojevi. Nemaju ogranicenje.
    3. `Float` - realni brojevi sa jednostrukom tacnoscu.
    4. `Double` - realni brojevi sa dvostrukom tacnoscu.
    5. `Bool` - vrednosti `True` i `False`.
    6. `Char` - karakteri
    7. Torke su tipovi, ali ih ima beskonacno mnogo kako su proizvoljne duzine
       i proizvoljnog redosleda parametara. `()` jeste tip i predstavlja samo
       jedinstvenu vrednost `()`

### Promenljivi tipovi

```haskell
Prelude> :t head
head :: [a] -> a
```
* Tip funkcije `head` je `[a] -> a`. Kako smo rekli da tipovi pocinju velikim 
  slovom, sta onda predstavlja `a` u tipu funkcije `head`?
* Kako ne pocinje velikim slovom `a` predstavlja *promenljivi tip*, tj. `a`
  moze biti bilo koji tip.
* Funkcije koje imaju promenljive tipove se nazivaju *polimorfne funkcije*.
* Promenljivim tipovima se po konvenciju daju imena `a`, `b`, `c`,...
```haskell
:t fst
fst :: (a, b) -> a
```
* Tip funkcije `fst` je `(a, b) -> a`, sto znaci da `fst` vraca vrednost
  koja je istog tipa kao i prva vrednost u paru `(a, b)`. Naravno `a`, i `b`
  mogu biti istog tipa.

### Tipovske klase

* Tipovske klase su kao interfejsi koji opisuju neko ponasanje. Ako tip 
  pripada nekoj tipovskoj klasi onda on mora da podrzava i implementira 
  ponasanja koja ta tipovska klasa opisuje.
```haskell
Prelude> :t (==)
(==) :: Eq a => a -> a -> Bool
```
* !Opasnost:
  * Kako je `==` infiksna funkcija, onda njen tip moramo naci tako sto je 
    prebacimo u neku drugu prefiksnu funkciju, ovde smo to ucinili tako sto
    smo je ubacili u zagrade.
* Ovde se javlja novi simbol `=>`, sve ispred njega se se naziva *ogranicenje
  klase*, dok je nakon njega tip funkcije.
* Ovo citamo kao: Funkcija jednakosti `(==)` prima bilo koje dve vrednosti 
  ista tipa, i vraca vrednost tipa `Bool`, pri tome da su te dve vrednosti 
  clanovi `Eq` klase.
* Osnovne tipovske klase:
  1. `Eq` se koristi za tipove koji podrzavaju testiranje jednakosti.
    * Funkcije koje implementiraju njeni clanovi su `==` i `/=`.
  2. `Ord` se koristi za tipove koji se mogu porediti.
    * Funkcije koje implementiraju njeni clanovi su `<`, `<=`, `>`, `>=`.
    * `Ordering` je tip koji moze da ima vrednosti `LT`, `GT`, `EQ`.
  3. `Show` se koristi za tipove koji se mogu predstaviti preko stringa.
    * Funkcija koju implementiraju njeni clanovi je `show`.
  4. `Read` se koristi za tipove koji se mogu dobiti od stringa.
    * Funkcija koju implementiraju njeni clanovi je `read`.
    * Kako je tip funkcije `read` `Read a => String -> a`, onda pri koriscenju
      ove funkcije moramo navesti koji se tip dodeljuje promenljivom tipu `a`.
      * `read "5" :: Int``
  5. `Enum` se koristi za tipove koji se mogu enumerisati.
    * Funkcije koje implementiraju njeni clanovi su `succ`, `pred`.
    * Omogucavaju da se koriste liste opsega.
    * Tipovi koji pripadaju ovoj klasi su: `()`, `Bool`, `Char`, `Ordering`,
      `Int`, `Integer`, `Float`, `Double`
  6. `Bounded` se koristi za tipove koji se mogu ograniciti (odozgo i odozdo).
    * Funkcije koje implementiraju njeni clanovi su `minBound` i `maxBound`.
    * Pored primitivnih tipova torke su takodje clanovi ove tipovske klase.
  7. `Num` se koristi za tipove koji se ponasaju kao brojevi.
    * Tipovi koji su clanovi ove klase: `Int`, `Integer`, `Float`, `Double`.
    * Da bi neki tip pripadao `Num` mora da pripada i `Show` i `Eq` klasi.
  8. `Integral` se koristi za tipove koji se ponasaju kao celi brojevi.
    * Tipovi koji su clanovi ove klase: `Int`, `Integer`.
  9. `Floating` se koristi za tipove koji se ponasaju kao realni brojevi.
    * Tipovi koji su clanovi ove klase: `Flaot`, `Double`.
* Korisna funkcija je `fromIntegral` koja prima neki ceo broj i prebacuje ga
  u broj kako bi mogao da se koristi generalnije.
  * Primer: `fromIntegral (length [1,2,3]) + 3.2`

## Sintaska u Funkcijama

### Pattern Matching




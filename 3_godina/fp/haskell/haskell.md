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

## Funkcije viseg reda

* Funkcije mogu primite druge funkcije kao argumente, i mogu vratiti 
  funkcije kao izlaz.

### Prenesene funkcije

* Svaka funkcija u haskelu ima jedan parametar!
  * Kako se onda definisu funkcije koje imaju vise parametara?
* Sve funkcije koje primaju vise parametara se nazivaju *prenesene funkcije*.
* `max 5` vraca funkciju koja vraca `5` ako je vrednost njenog argument 
  manja od `5` ili vraca vrednost tog argumenta. Pa je onda `max 5 2` 
  ekvivalentno sa `(max 5) 2`.
    * Postavljanje razmaka izmedju dve stvari je **primenjivanje funkcije**.
* Tip funkcije `max` je `(Ordering a) => a -> a -> a` sto je efektivno
  `(Ordering a) => a -> (a -> a)`.
* Ako pozovemo funkciju sa manje parametara nego sto ona prima, dobijemo
  **parcijalno primenjenju funkciju**, koja prima ostatak parametara.

### Vise od viseg reda

* Funkcije mogu primiti druge funkcije kao parametre.

```haskell
applyTwice :: (a -> a) -> a -> a
applyTwice f x = f (f x)
```
* U ovom slucaju funckija prima drugu funkciju tipa `(a -> a)`, i od nje
pravi funkciju tipa `a -> a`.

### Mape i Filteri

* `map` prima funkciju i listu i na svaki element liste primenjuje tu funkciju.
```haskell
map' :: (a -> a) -> [a] -> [a]
map' _ [] = []
map' f (x:xs) = f x : map' f xs
```

* `filter` je funkcija koja prima predikat i listu i generise novu listu 
  sa elementima za koje vazi predikat.
```haskell
filter' :: (a -> Bool) -> [a] -> [a]
filter' _ [] = []
filter' pred (x:xs) 
    | p x       = x : filter' xs
    | otherwise = filter' xs
```

* `takeWhile` je funkcija koja prima predikat i listu i generise novu listu
  sve dok na trenutnom elementu vazi predikat.

### Lambde

* Lambda funkcije su anonimne funkcije (nemaju ime), koje se koriste samo
  jednom pa nam njihovo ime nije potrebno.
* Sintaksa lambda funkcije je da se na pocetku stavi simbol `\` zato sto 
  nekako lici na lambdu, a da se onda navedu argumenti razdvojeni razmakom, 
  nakon cega je `->` i onda telo funkcije.
  * Obicno lambda funkcije zagradjujemo zagradama sem ako se ne prostiru do 
    kraja naredbe.
* Primeri: 
  * `(\xs -> length xs > 15)`
  * `(\a b -> a + b)`
  * `addThree x y z = x + y + z` je ekvivalentno sa `addThree \x -> \y -> \z -> x + y + z`

### Fold

* Kao sto se moze primetiti `(x:xs)` je vrlo cest patern, pa kako se ne bi
  pisao stalno i kako bi se smanjila rekurzija koriste se funkcije koje
  zovemo *foldovi*.
* Foldovi uzimaju binarnu funkciju (funkciju dva argumenta), startnu vrednost
  (akumulator), i listu vrednosti. Binarna funkcija se poziva na prvi element
  i akumulator i dobija se novi akumulator, ovaj proces se nastavlja za o
  statak liste, sve dok se ne dodje do poslednjeg elementa, i ostane samo
  akumulator.
* `foldl` je funkcija koja se jos i naziva levi fold. On umotava listu sa
  leve strane. Binarna funkcija se primenjuje na pocetnu vrednost i glavu
  funkcije i dobija se novi akumulator. Binarna funkcija se dalje primenjuje
  na sledeci element i akumulator, te se opet dobija novi akumulator, itd...
```haskell
sum' :: (Num a) => [a] -> a
sum' xs = foldl (\acc x -> acc + x) 0 xs
sum' = foldl (+) -- kompaktniji zapis

elem' :: (Eq a) => a -> [a] -> Bool
elem' y xs = foldl (\acc x -> if x == y then True else acc) False xs
```

* `foldr` je slican funckiji `foldl` sem sto se umotavanje izvrsava sa 
  desne strane. Binarna funkcija za prvi parametar ima zadnji element liste
  dok je drugi parametar akumulator, sto i ima smisla jer akumulator 
  umotava sa desne strane.
  * `foldr` moze da radi na beskonacnim listama, dok `foldl` ne moze, 
    sto ima smisla.

```haskell
map' :: (a -> b) -> [a] -> [b]
map' f = foldl (\acc x -> acc ++ [f x]) []  -- ++ je skupa operacija
map' f = foldr (\x acc -> f x : acc) []     -- : je jeftina operacija
```

* **Foldovi se mogu koristiti za implementiranje bili kojih funkcija koje
  prolaze kroz listu jednum, element po element, i vracaju nesto na osnovu
  toga. Kad god prolazis kroz listu i zelis da vratis nesto, velike su 
  sanse da hoces da koristis fold.**

* `foldl1` i `foldr1` su funkcije slicne kao `foldl` i `foldr` sem sto
  nemaju pocetnu vrednost akumulatora vec je pocetna vrednost akumulatora
  prvi element liste.
  
```haskell
maximum' :: (Ord a) => [a] -> a
maximum' = foldl1 (\acc x -> if x > acc then x else acc)

reverse' :: [a] -> [a]
reverse' = foldr (\x acc -> x : acc) []

product' :: (Num a) => [a] -> a
product' = foldl1 (*)

filter' :: (a -> Bool) -> [a] -> [a]
filter' pred = foldr (\x acc -> if pred x then x : acc else acc) []

head' :: [a] -> a
head' = foldr1 (\_ acc -> acc)

last' :: [a] -> a
last' = foldl1 (\x _ -> x)
```

* `scanl` i `scanr` su slicni `foldl` i `foldr` sem sto oni 
  vracaju listu trenutnih stanja akumulatora u svakom koraku.
  * Takodje, postoje odgovarajuci `scanl1` i `scanr1`.

### Primenjivanje funkcije sa `$`

* Funkcija `$` se naziva *funkcija primene* i definisana je kao
```haskell
($) :: (a -> b) -> a -> b
f $ x = f x
```
* Ova funkcija sluzi da bi se promenio prioritet primene funkcija
  tako da normalno primenjivanje funkcija je levo asocijativno,
  primenjivanje funkcija pomocu simbola `$` je desno asocijativno.
  * Zbog toga je `sum (map sqrt [1..10])` ekvivalentno sa 
    `sum $ map sqrt [1..10]`

### Kompozicija funkcija

* Kompozicija funkcija u haskelu je ista kao i u matematici.
* Operator kompozicije `.` je definisan kao:
```haskell
(.) :: (b -> c) -> (a -> b) -> a -> c
f . g = \x -> f (g x)
```
* Izraz `negate . (*3)` je funkcija koja uzima broj mnozi ga sa 3
  i onda ga negira.
* Zapisimo ovo preko kompozicija funkcija 
  `f x = ceiling (negate (tan (cos (max 50 x))))`
  * Dobijamo
  `f = ceiling . negate . tan . cos . max 50`

## Konstrukcija tipova i Klasnih tipova

### Algebarske tiovi podatak

* Jedan nacin definisanja tipa je koriscenjem kljucne reci `data`
```haskell
data Bool = True | False

data Int = -2147483648 | -2147483647 | ... | -1 | 0 | 1 | 2 | ... | 2147483647

data Shape = Circle Float Float Float | Rectangle Float Float Float Float
```

* `data` znaci da definisemo novi tip, nakon cega sledi ime tipa
  koje se pise velikim slovom, a nakon imena je `=`, nakon cega 
  je **konstruktor vrednosti**. Simbol `|` se cita *ili*.
* `Shape` predstavlja ili `Circle` ili `Rectangle`, ali nakon
  njim imamo Float tipve. (Zasto?) Kako bih obezbedili nacin
  na koji se konstruise `Circle` specifikujemo dodatna tri `Float`
  nakon definisanja njegovog imena, slicno za `Rectangle`.
* `Circle` i `Rectangle` su nista drugo no funkcije od kojih 
  se dobija `Shape`.
```haskell
Prelude> :t Circle
Circle :: Float -> Float -> Float -> Shape
Prelude> :t Rectangle
Rectangle :: Float -> Float -> Float -> Float -> Shape
```

### Slog sintaksa

```haskell
data Person = Person { firstname :: String
                     , lastname :: String
                     , age :: Int
                     , height :: Float
                     , number :: String
                     , icecream :: String
                     } deriving (Show)
```

```haskell
*Main> let guy = Person "Pera" "Peric" 32 180.0 "0641112233" "Vanila"
*Main> lastname guy
"Peric"
*Main> icecream guy
"Vanila
*Main> guy
Person {firstname = "Pera", lastname = "Peric", age = 32, height = 180.0, number = "0641112233", icecream = "Vanila"}
```

### Tipovski parametri

* **Tipovksi konstruktor** uzima tipove kao parametre i od njih 
  pravi nove tipove.
```haskell
data Maybe a = Just a | Nothing
```
* U ovom primeru je `Maybe` tipovski konstruktor koji uzima 
  parametar `a`.
  * Sve sto je levo od `=` je tipovski konstruktor, a sve sto je
    desno od `=` je konstruktor vrednosti razdvojen sa `|`.
```haskell
data Vector a = Vector a a a deriving (Show)

vecSum :: (Num a) => Vector a -> Vector a -> Vector a
vecSum (Vector x y z) (Vector a b c) = Vector (x+a) (y+b) (z+c)

vecMult :: (Num a) => Vector a -> a -> Vector a
vecMult (Vector x y z) a = Vector (a*x) (a*y) (a*z)
```

### Izvedene instance

* Tip je **instanca** neke tipovske klase ako podrzava to ponasanje.
* Za izvodjenje neke klase kao instance nekog tipa koristi se
  kljucna rec `deriving` a nako nje u zagradima se navode
  tipovske klase koja onda izvodi razdvojene zarezom.
* Primer bez definisanje operacija `==` i `/=` kada `Person` izvodi
  klasu `Eq`.
  * U ovom slucaju se koristi *default* operacija `==` i 
    `/=` primitivnih tipova.
```haskell
*Main> let guy1 = Person "Pera" "Peric" 32 180.0 "0641112233" "Vanila"
*Main> let guy2 = Person "Pera" "Zdera" 32 180.0 "0641112233" "Vanila"
*Main> guy1 == guy2
False
```
```haskell
data Dan = Ponedeljak | Utorak | Sreda | Cetvrtak | Petak | Subota | Nedelja deriving (Show, Read, Eq, Ord, Bounded, Enum)
```
```haskell
*Main> Nedelja
Nedelja
*Main> show Nedelja
"Nedelja"
*Main> read "Nedelja" :: Dan
Nedelja
*Main> compare Nedelja Ponedeljak
GT
*Main> Nedelja == Ponedeljak
False
*Main> minBound :: Dan
Ponedeljak
*Main> maxBound :: Dan
Nedelja
*Main> pred Nedelja
Subota
*Main> succ Ponedeljak
Utorak
*Main> [Ponedeljak .. Petak]
[Ponedeljak,Utorak,Sreda,Cetvrtak,Petak]
```

### Tipovski sinonimi

* `[Char]` i `String` su ekvivalentni i mogu se koristiti bilo kako.
* Ovi tipovi se nazivaju **sinonimi**. Sluze samo za drugo imenovanje
  istog tipa.
* Definisu se pomocu kljucne reci `type` nakon cega je ime sinonima,
  nakon cega je `=`, nakon cega je neki drugi vec definisan tip.
```hasekll
type Ime = String
type Broj = String
type Imenik = [(Ime, Broj)]

uImeniku :: Ime -> Broj -> Imenik -> Bool
uImeniku ime broj imenik = elem (ime, broj) imenik
```
* Sinonimi takodje mogu biti parametrizovani
```haskell
type AsoccList k v = [(k,v)]
```
* Jos jedan kul tip je `Either a b`:
```haskell
data Either a b = Left a | Rigth b deriving (Show, Read, Eq, Ord)
```
* Dok se `Maybe` koristi kao povratna vrednost neke funkcije koja
  moze da se ne izracuna, `Either` se koristi u funkcijama za koje
  zelimo da znamo zbog cega nesto nije mogulo da se izracuna.
  Pa tako povratnu vrednost postavljamo na `Right`, dok razlog greske
  ukoliko postoji postavljamo na `Left`.
```hasekll
data OrmaricStanje = Zauzeto | Slobodno deriving (Show, Eq, Ord)

type Kod = String
type OrmaricMapa = Map.Map Int (OrmaricStanje, Kod)

pregledOrmarica :: Int -> OrmaricMapa -> Either String Kod
pregledOrmarica brojOrmarica mapa =
    case Map.lookup brojOrmarica mapa of
        Nothing -> Left $ "Ormaric broj " ++ show brojOrmarica ++ " ne postoji!"
        Just (stanje, kod) ->
            if stanje == Zauzeto
                then Left $ "Ormaric broj " ++ show brojOrmarica ++ " je zauzet!"
                else Right kod
```


### Rekurzivne strukture podataka

```haskell
infixr 5 :+:
data Lista a = Prazna | a :+: (Lista a) deriving (Show, Read, Eq, Ord)

data Drvo a = PraznoDrvo | Cvor a (Drvo a) (Drvo a) deriving (Show, Read)

noviCvor :: a -> Drvo a
noviCvor x = Cvor x PraznoDrvo PraznoDrvo

ubaciCvor :: (Ord a) => a -> Drvo a -> Drvo a
ubaciCvor x PraznoDrvo = noviCvor x
ubaciCvor x (Cvor a levo desno)
    | x == a = Cvor x levo desno
    | x < a  = Cvor a (ubaciCvor x levo) desno
    | x > a  = Cvor a levo (ubaciCvor x desno)

elemtCvor :: (Ord a) => a -> Drvo a -> Bool
elemtCvor x PraznoDrvo = False
elemtCvor x (Cvor a levo desno)
    | x == a = True
    | x < a  = elemtCvor x levo
    | x > a  = elemtCvor x desno
```

### Tipovske klase 102

```haskell
class Eq a where
    (==) :: a -> a -> Bool
    (/=) :: a -> a -> Bool
    x == y = not (x /= y)
    x /= y = not (x == y)

data Semafor = Crveno | Zuto | Zeleno deriving (Show)

instance Eq Semafor where
    Crveno == Crveno    = True
    Zuto   == Zuto      = True
    Zeleno == Zeleno    = True
    _      == _         = False 

instance Show Semafor where
    show Crveno = "Crveno svetlo"
    show Zuto   = "Zuto svetlo"
    show Zeleno = "Zeleno svetlo"
```

### Da-Ne klasa tipova

```haskell
class DaNe a where
    dane :: a -> Bool

instance DaNe Int where
    dane 0 = False
    dane _ = True

instance DaNe [a] where
    dane [] = False
    dane _  = True

instance DaNe Bool where
    dane = id

instance DaNe (Maybe a) where
    dane Nothing  = False
    dane (Just _) = True

instance DaNe (Drvo a) where
    dane PraznoDrvo = False
    dane _          = True

instance DaNe Semafor where
    dane Crveno = False
    dane _      = True
```
```haskell
*Main Map> dane Crveno
False
*Main Map> dane (Just 3)
True
*Main Map> dane (Nothing)
False
*Main Map> dane (PraznoDrvo)
False
*Main Map> dane (noviCvor 2)
True
*Main Map> dane True
True
*Main Map> dane False
False
*Main Map> dane []
False
*Main Map> dane [1,2,3]
True
```

### Funktor tipovska klasa

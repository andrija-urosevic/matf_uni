# Uvod u racunarske mreze

## Nacin rada u mrezi

* Klijent-Server okruzenje:
  * *server* pruza resurse
  * *klijent* kontaktira server za koriscenje tih resursa
* Mreza ravnopravnih racunara (P2P):

## Komponente racunarske mreze

* Mrezni hardver
* Komunikacioni kanali
* Mrezni softver

### Mrezni hardver

* *Mrezna kartica* (NIC - Network Interface Controller) je uredjaj u racunaru koji omogucava fizicki pristup mrezi.
* *MAC adresa* (Media Access Control address) se dodeljuje NICu i jedinstveno
  ga odredjuje
* *Modem* je uredjaj koji konvertuje digitalni signal u analogni koji se 
  prenosi, a zatim obrnuto konvertuje preneti analogni u digitalni.
* Hab, most, svic i ruter - mrezni hardver koji sluzi za prosledjivanje
  komunikacije izmedju racunara u mrezi

### Komunikacioni kanali

* *Komunikacioni kanali* su kablovi ili bezicni medijumi koji prenose
  podatke elektromagnetnim talasima.
* Mera kvaliteta komunikacionog kanala:
  * *Protok* (bardwidth) meri broj bitova koji se mogu preneti u jednoj
    sekundi (bit/s)
    * Zavisi od frekvencije elektromagnetnih talasa na kojima se koristi.
  * *Kasnjenje* (latency) meri vreme potrebno da se komponenta pripremi
    za pristup podacima
* *Ukrstene parice*:
  * Najcesci nacin komunikacije
  * Ubijene uparene izolovane bakarne zice 
  * UTP kablovi (unshielded twisted pair)
  * 100 Mbps pa do 1 Gbps
* *Koaksijalni kablovi*:
  * Televizijski kablovski sistemi
  * Centralna bakarna ili aluminijumska zica obmotana izolacionim slojem,
    pa obmotan provodni sloj tankih zica, pa opet izolacioni sloj
  * 200 Mbps pa do 500 Mbps
* *Opticki kablovi*:
  * Veliki broj tankih staklenih vlakana umotanih u zastitan sloj
  * Podaci se prenose pomocu svetlosti koje emituje laser.
  * Koriste se za brze mreze od 10 Gbps pa navise.
* *Bluetooth*:
  * Komunikacija na malim razdaljinama
  * Oko 3 Mbps
* *Bezicni LAN, WLAN*:
  * Bezicna komunikacija vise uredjaja na ogranicenom rastojanju
  * 10 Mbps do 50 Mbps i do 600 Mbps
  * Pristupa se na access point
  * Oblast gde se moze pristupiti se naziva hot spot
* *Bezicne gradske mreze, WiMAX*:
  * Pokrivaju siru oblast
  * 40 Mbps
* *Celijski sistemi*:
  * Nacin prenosa slican u mobilnoj telefoniji
  * Od odredista do celije se prenosi preko niza antena
* *Zemaljski mikrotalasi*:
  * Rade pomocu mikrotalasa niske frekvencije koje zahtevaju opticku
    vidljivost pa se zbog toga postavljaju na visokim tackama.
* *Komunikacioni sateliti*:
  * Koriste mikrotalase tako sto se prepreka opticke vidljivosti
    resava tako se se signal prenosi preko niza satelita.
  * 100 Mbps

### Mrezni softver

* Omogucava funkcionisanje racunarskih mreza.
* Sloj: Softverski sloj i hardverski sloj.
* Mrezni softver niskog nivoa, obicno su to driveri u jezgru operativnog 
  sistema.
* Mrezni softver pruza usluke mreznim aplikacijama koje koristi korisnik.

## Raspon racunarske mreze

* *Hijerarhija umrezavanja*:
  * Mreze velikog raspona povezuju manje mreze.
* Prema rasponu mreze klasifikujemo:
  1. *Personal Area Network (PAN)*
    * mreza za jednog coveka
    * na primer: racunar, mis i stampac cine jedan PAN
  2. *Local Area Network (LAN)*
    * mreza koja povezuje uredjaje na relativno maloj udaljenosti
  3. *Campus Area Network (CAN)*
    * mreze koje povezuju vise lokalnih mreza u okviru odredjenog
      geografskog prostora
    * na primer: kompanija, univerzitet,...
  4. *Metropolitan Area Network (MAN)*
    * povezuje vece geografske prostore
    * Povezuje vise LANa koriscenjem optickih kablova kao kicme.
  5. *Wide Area Network (WAN)*
    * one povezuju izrazito velike geografske prostore
    * obicno ih odrzavaju telekomunikacione kompanije.

## Topologija racunarskih mreza

* Topologija mreze predstavlja nacin na koji su komponente mreze povezane
  medju sobom, kao i nacin na koji komuniciraju.
* Dva nivoa:
  1. Fizicka topologija - raspored kablova i bezicnih veza
  2. Logicka topologija - tok podataka
* Dva kljucna nacina povezivanja:
  1. Zajednicki komunikacioni kanala (broadcast)
  2. Direktna veza od cvora do cvora (point-to-point)

### Zajednicki komunikacioni kanala

* Racunari salju pakete na mreze postavljajuci ih na komunikacioni kanal 
  pri cemu paket sadrzi podatke i identifikator primaoca
* Podatke svi primaju, pri cemu je jednio prihvata onaj kome je ona namenjena
* Staticki - svaki uredaj ima unapred odredjena praviliak u kom delu kanala
  sme da vrsi komunikaciju
* Dinamicki - pristup uredjaja kanalu se odredjuje na osnovu trenutnog stanja
  i dostupnosti kanala.
* Deljenje zajednickog kanala:
  1. Deljenje vremena (Time Division Multiplexing - TDM):
    * svaki uredjaj komunicira u odredjenom trenutku
  2. Deljenje frekvencije (Frequency Division Multiplexing - FDM):
    * svaki uredjaj komunicira na svom opsegu frekvencije
  3. Deljenje talasne duzine (Wawe Devision Multiplexing - WDM):
    * svaki uredjaj komunicira na svom opsegu talase duzine
  4. Deljenje kodiranjem (Code Devision Multiple Access - CDMA):
    * iz paketa se izdvajaju informacije relevantne za odredjeni cvor
  5. CSMA/CD (Carrier Sense Multiple Access with Collision Detection)
    * svaki uredjaj posmatra da li kroz kanal protice neka komunikacija
      pre nego sto pocne da selje podatke
    * ukoliko se primeti da neko drugi salje podatke, uredjaj saceka pa
      proba ponovo nakon odredjenog vremena
* Razlikuju se 4 tipa topologija mreze:
  1. *Magistrala*:
    * mreza se povezuje jednim istim kablom koji se naziva magistrala
  2. *Zvezda*:
    * svi su povezani na jednu istu centralnu tacku, a informacija
      putuje od posiljaoca prema primaocu pre nje.
  3. *Prsten*:
    * sve komponente su na istom kablu ali taj kabal nema krajeve pa 
      formira prsten, dok se informacija krece u jednom pravcu
  4. *Potpuna povezanost*:
    * svaki cvor ima posebnu vezu sa svakim drugim cvorom.

### Direktne cvor-cvor veze

* Mreza se sastoji od velikog broja direknih veza izmedju parova racunara
* Informacija prolazi kroz niz cvorova
* Koristi se u okviru velikih mreza
* Izbor pogodne putanje obicno veoma znacajan za efikasnu komunikaciju
* Komutiranje (switching): Odredjuje putanju pre ili tokom same komunikacije
* Tipovi komunikacije:
  1. *Komutiranje kanala* (Circuit Switching):
    * pre zapocinjanja komunikacije ostvaruje se trajna fiksiranja putanja
      izmedju cvorova i informacija se prosledjuje kroz tu putanju
  2. *Komutiranje poruka* (Message Switching):
    * svaka poruka putuje zasebnom putanjom
  3. *Komutiranje paketa* (Packet Switching):
    * poruka se pre slanja dele na zasebne manje pakete, i svaki putuje 
      svojom zasebnom putanjem
      * delovi mogu da putuju zasebno

## Slojevi mreza

* Mreze se grade hijerarhijski gde svaki deo hijerarhije prestavlja
  po jedan sloj
* Na svakom sloju sprovodi se odgovarajuci protokol komunikacije
* Protokol je dogovor dve strane o nacinu komunikacije
* Mreze se posmatraju u okviru dva referentna modela:
  1. *OSI model* (Open System Interconnection) sa 7 slojeva,
    standardizovan od stranje ISO
  2. *TCP/IP model* sa 4 sloja, prisutak u okviru Interneta

### OSI model

1. *Fizicki sloj* (Physical layer)
  * obezbedjuje postojanje komunikacionog kanala i mogucnost slanja i 
    primanja pojedinacnih bitova kroz komunikacioni kanal
2. *Sloj veze podataka* (Data Link Layer)
  * obezbedjuje visim slojevima postojanje pouzdanog kanala komunikacije
    u kome se:
    * greske detektuju i ispravljaju (error control)
    * vodi se racuna o brzini slanja podataka (flow control)
3. *Mrezni sloj* (Network Layer)
  * *Rutiranje* (Routing) odredjivanje putanje paketa koji putuju
    kroz mrezu
  * Prevodjenje adresa (MAC u IP ili obrnutu)
  * Internet Protocol (IP)
4. *Transportni sloj* (Transport Layer)
  * prihvata podatke sa visih slojeva i deli ih na pakete,
    te salje pakete pomocu nizih slojeva
  * protokoli sa uspostavljanjem konekcije garantuju da se poslati podaci
    stici na odrediste u istom redosledu u kojem se poslati
  * protokol bez uspostavljanja konekcije ne daju ovakve garancije, ali
    dobija se na brzini
  * protokoli koji komuniciraju dva host racunara
  * vrse multipleksiranje preko *portova*
  * *Transfer Control Protokol* (TCP) i *User Datagram Protocol* (UDP)
5. *Aplikacioni sloj* (Application Layer)
  * protokoli koji direktno koriste korisnicke aplikacije u okviru svoje
    komunikacije
  * protokoli u kojima dva programa/aplikacije komuniciraju
  * HyperText Transfer Protocol (HTTP) - web stranice
  * SMTP, POP3, IMAP - email
  * File Transfer Protocol (FTP) - prenost podataka

# Internet, usluge i protokoli



# Jezici za obelezavanje

# Programski jezik JavaScrip

## Uvod

* JavaScript je jedini script jezik koji je podrzan na svim pretrazivacima.
* Omoguciva animacije i dinamicki HTML kao i jos puno drugih stvari
* Node.js omogucava razvoj na serverskoj strani

## Karakteristike jezika JavaScript

1. *Jezik viskokog nivoa*
2. *Dinamican*
3. *Dinamicki tipiziran*
4. *Slabo tipiziran*
5. *Interpretiran*
6. *Podrzava vise paradigmi*

## JavaScript okruzenje za izvrsavanje

* JS Runtime Enviroment
* Postoje dva tipa: ugradjen u pretrazivacu (za rad sa klijentom) i node.js
  (za rad sa serverom)
* JS Engine
  * Pisan u C++ i izvrsava JavaScript kod
  * just-in-time compilation
  * V8, Rhino, SpiderMonkey, Chakra
  * Hip
    * cuva dinamicke podatke (objekte)
  * Stek
    * privremeno cuva podatke (funkcije, argumente, i lokalne promenljive)
* External APIs
  * Sadrzi spoljasnji objekti i metode koji omogucavaju komunikaciju sa 
    spoljnim svetom.
* Callbeck Queue
  * Deo koda koji ceka na redu da se posalje na izvrsavanje JS Engine-u
  * Kod koji se uzima smesta se na stek, a za to odlucuje event loop
* Event loop
  * Proces koji stalno proverava da li je stek prazan i da li postoje
    neke funkcije u redu koje su spremne za izvrsavanje.

# Struktura JavaScript programa

### Osnovni elementi jezika JavaScript

* Unicode znaci
* Tacna-zarez
  * Nije potrebna dovoljno je imati novi red kako bi predstavili kraj 
    neke naredbe, ali isto tako i nije pogresno
* Beline
  * Razmak, Tabuliranje, Nova linija, itd.
  * U teoriji nemaju znacenje, ali se koriste u praksi
* Razlikuje velika i mala slova kao posledica unicode znaka
* Komentari
  * blokovski: `/* komentar */`
  * linijski: `// komentar`
* Literali
  * Niz znakova koji predstavlja vrednost upisanu u samom izvornom kodu
  * `5`, `'niska'`, `true`, `['a', 'b']`, `{boja: 'crvena', oblik: 'trougao'}
* Identifikatori
  * Sekvenca znakova koja se moze koristiti za identifikaciju promenljivih,
    funkcija ili objekata
  * pocinju slovom ili `$` ili `_ ` a ostali deo je bilo koji unikod znak
  * `test1`, `Test2`, `$test5`, itd.
* Rezervisane reci
  * Rezervisane su za konstrukcije JavaScrip jezika i ne mogu se koristiti
    kao identifikatori

## Tipovi i vrednosti

* Tipove u JavaScript delimo na dve osnovne grupe:
  1. Primitivni tipovi
  2. Objektni tipovi

### Primitivni tipovi

* Brojevni tipovi (`Number`)
* Niska tipovi ('string')
* Logicki tipovi ('boolean')
* Simboli ('symbol')
* `null`
* `undefined`

### Brojevi

* Mogu biti literal koji je predstavljen kao broj sa fiksinm zarezom ili broj 
  u pokretnom zarezu.
```
42      // fiksnom zarezu 
0x321   // fiksnom zarezu 
9.81    // pokretnom zarezu
.23     // pokretnom zarezu
23.23e8 // pokretnom zarezu
```

### Niske

* Sekvenca znakova, koje se zapisuju u `''`
* Postoje posebni znakovi koji se nazivaju eskejp-sekvence koje pocinju
  znakom `\` pa obicno nekim drugim slovom. Ako zelimo da na primer
  imamo `\n` u tekstu onda moramo koristiti `""` oko njih.

### Logicki tipovi

* `true` i `false`
* Operatori kao sto su `==`, `===`, `<`, `>`, `<=`, `>=`, vracaju vrednosti
  logickog tipa.

### Specijalni tip null

* Predstavlja vrednost koja ukazuje na nepostojanje vrednosti

### Specijalni tip undefined

* Predstavlja vrednost koja nije inicijalizovana ili da nedostaje njena 
  vrednost

### Objektni tipovi

* Sve sto nije primitivni tip predstavlja objektni tip
* To su funkcije, nizovi i objekti.
* Svi oni imaju osobine i metode
* Slicno rede kao u Javi
* Specijalno postoje i `String`, `Number`, i `Boolean` koji predstavljaju
  odgovarajuce nemutirajuce primitivne tipove

## Promenljive

* Imenovane lokacije u memoriji
* Njihova vrednost se menja, pa otuda i njihov naziv
* Deklaracija, Inicijalizacija i sve te lepe stvari vaze.

### Opseg definisanosti i konteksti

* Opseg definisanosti promenljive (scope) je vezan za pojam promenljive i
  predstavlja deo programskog koda u kojoj je neka promenljiva vidljiva i 
  dostupna za rad.
* Prema *vremenu definisanje* opseg definisanosti moze biti:
  * Staticki opseg definise se u trenutku prevodjenja, tako da funkcija tada
    zapamti reference na koje ukazuje promenljive u lanuc opsega (early 
    binding).
  * Dinamicki opseg definise se u vreme izvrsavanja koda, pa se vezuje za 
    reference na koje ukazuju promenljive u tom trenutku kada se izvrsava
    kod (late binding).
* Prema *velicini* opseg difinisanosti moze biti:
  * Lokalni opseg
  * Funkcijski opseg
  * Blokovski opseg
  * Globalni opseg 

## Izrazi

* Delovi programskog koda koji mogu biti evaluirana, tj. cija se vrednost
  moze izracunati.
1. Izrazi sa bocnim efektima
2. Izrazi bez bocnog efekta
* Kategirije:
  * Primarni izraz
  * Aritmeticki izraz
  * Niska-izrazi
  * Logicki izrazi
  * Izrazi leve strane

### Prioritet operatora

* Odredjuje kojim ce se redom operatori primenjivati. To se postize
  tako sto svaki operator ima svoj nivo prioriteta i svoje pravilo
  asicijativnosti

## Konverzija tipova i evaluacija izraza

### Eksplicitna konverzija tipa

* Promena tipa podataka neke promenljive, obicno se koriste odredjene
  ugradjene funkcije:
  * `String()`, `toString()`
  * `Number()`, `parseFloat()`, `parseInt()`
  * `Boolean()`

### Implicitna konverzija tipa

* Desava se kao sporedni efekat nikih drugih radnji.

## Naredbe i sekvence naredbi

### Naredbe dodele vrednosti

* Koristi se operator `=`.

### Kombinovane naredbe dodele

* Koristie se operatori: `+=`, `-=`, `*=`, `/=`, `%=`, `<<=`, `>>=`, `>>>=`,
  `&=`, `^=`, `|=`, `**=`

### Naredbe inkrementiranja i dekrementiranja

* `++` uvecaj za 1 i `--` umanji za 1.

### Pozivi predefinisanih funkcija

* Ugradjeni objekti sa njihovim osobinama i metodama
  * `Array`, `Math`, `Date`, `Function`, `String`, `Number`

### Grananje

* `if (uslob) {blok}`, `if (uslob) {blok} else {blok}`, 
  `if (uslov) {blok} else if (uslov) {blok} else if (uslov) {blok} else {blok}`
* `switch (promenljiva) case vrednost1: blok; case vrednost2: blok;...default: blok`

### Ciklusi

* `while (uslov) {blok}`
* `do {blok} while (uslov)`
* `for (init; uslov; action) {blok}`
* Iz ciklus se moze prekinuti naredbom `break`
* Preskakanje iteracije se postize naredbom `continue`
* Moguce je i obelezeno prekidanje i preskakanje iteracije ali se ne koristi
  toliko cesto

# Funkcije i zatvorenja

* Funkcije karakterise da su gradjani prvog reda (first class citizen)
* Ako je programski entitet gradjanin provg reda, tada entitet podrzava
  sve operacije dostupne drugim tipovima i moze da se ponasa potpuno isto
  kao bilo koja druga vrsta entitata koja je gradjanin prog reda.
* Funkcije zato imaju sve osobine primitivnih tipova i sve osobine objekta.
* Funkcije se definisu pomocu deklaracije i pomocu funkcijskog izraza.

## Deklaracija i poziv funkcije

```
function name(param1, param2, ...) {
    var local1
    ...
    return returnVal
}
```
* Svaka funkcija ima parametre koje su vrednosti koje dobija van svog bloka
* Takodje u svom bloku moze imati lokalne promenljive.
* Funkcija moze da ima povratnu vrednost koja se vraca koriscenjem kljucne
  reci `return`.
* Funkcija se poziva tako sto se napise njeno ime i proslede parametri

## Funkcijski izrazi i poziv funkcije

* U ovom smislu je funkcija gradjanin prvog reda.
```
let name = function(param1, param2, ...) {
    var local1
    var loval2
    ...
    return returnVal
}
```
* Grubo receno, `name` je promenljiva koja referise na funkciju.
* Poziva se isto kao i deklarisana funkcija
* Vrsi se supstitucija po vrednosti

## Parametri i argumenti funkcija

* Ne moraju se poklopiti tipovi parametara sa tipovima argumentima pri pozivu,
  takodje ni broj argumenate ne mora da se poklapa se brojem parametara
* Ako je broj argumenata veci nego broj parametara visak se samo ignorise,
  u suprotnom oni koju su visak postaju undefined

## Opcioni parametri funkcija

* Parametar je opcioni, ako se u definiciji funkcije prvi navodjenju 
  prametra postavi njegova podrazumevana vrednost
```
const stepen = function (base = 10, exp = 2) {}
```

## Opsezi vazenja za promenljive i funkcije

* `let` i `const` imaju blokovski opseg promenljivih
* `var` ima funkcijski opseg promenljivih

## Stek poziv za funkcije

* Funkcija u svom telu moze sadrzati vise poziva drugih funkcija, ili
  moze da poziva samu sebe. Poziv funkcije i povrataka iz funkcije se postize
  koriscenjem stek-okvira (stack frame)

## Rekurzivne funkcije

* Rekurzija omogucava da funkcija u svojoj definicija poziva sama sebe.

## Lambda izrazi i funkcije

* Umesto kljucne reci `function` za definisanje funkcije se koristi operator
  `=>`.
* Ispred operatora `=>` se pisu parametri, a nakon njega se dalje zapisuju
  telo funkcije

## Zatvorenja za funkcije

* Sta se dogadja sa lokalom vezom kada funkcija koja je kreirala tu vezu vise
  nije aktivna, tj. kada je zavrsila sa radom?
```
function omotajVrednost(n) {
    let lokalnaPromenljiva = n;
    return () => lokalnaPromenljiva;
}

let omotacZa1 = omotajVrednost(1);
let omotacZa2 = omotajVrednost(2);

console.log(omotacZa1());
console.log(omotacZa2());
```

* Mogucnost da se referise na konkretno lokalno vezivanje u okruzujucem 
  opsegu se naziva zatvaranje (closure).
* Zatvorenja su funkcije koje imaju pristup promenljivima koje se nalaze u 
  opsegu definisanosti druge funkcije, sto se postize ugnjezdjivanje funkcije.
* Funkcija zatvorenja ima pristup memoriji na koju promenljiva referise
  u trenutku pozivanja.

## Funkcije kao generatori funkcija

```
function pronadjiResenje(cilj) {
    function pronadji(start, istorija) {
        if (start == cilj)
            return istorija;
        else if (start > cilj)
            return null;
        else
            return pronadji(start + 5, "(" + istorija + " + 5) ") ||
                pronadji(start * 3, "(" + istorija + " * 3) ");
    }
    return pronadji(1, "1");
}

for(let i=1; i<71; i++)
    console.log(i + " = "+ pronadjiResenje(i));
```

## Dizanje promenljivih i funkcija

* Princip dizanje promenljivih i funkcija (hoisting) se odnosi na deklarisanje
  promenljive ili funkcije bilo gde u kodu tako da ima isti efekat kao da je
  ta promenljiva deklarisana na pocetku programskog koda.
* Ne vazi za promenljive tipa `let` i `const`
```
// Ovo ne radi, daje gresku
console.log(x)
let x = 5

// Ovo radi, ali ne ispisuje 5 vec undefined
console.log(x)
var x = 5
```
* Dizanje funkcija se odvija pre dizanja promenljivih
```
// 2. Dizanje promenljive
// 3. Dodela promenljive
var test = function (){
  console.log("prikaz iz funkcijskog izraza");
}

// 1. Dizanje funkcije
function test(){
  console.log("prikaz iz deklarisane funkcije");
}

// 4. Izvrsavanje dodeljene promenljive
test();
```

## Funkcije i bocni efekti

* Funkcije mogu da se pozivaju zbog svojih bocnih efekata i zbog svojih
  povratnih vrednosti.
* Funkcija koja nema bocne efekte i ne oslanja se na rad drugih funkcija
  koje imaju bocne efekte se naziva cista funkcija.
* Osobina cistih funkcija je to da za iste argumente imaju iste povratne
  vrednosti
* Nekada nije moguce ili nije dovoljno koristiti uvek samo ciste funkcije.

# Objekti i nizovi

## Objekti

1. Objekti koje definise sam programer
2. Objekti ugradjeni u JavaScript (`String`, `Number`, `Array`, ...)
3. Objekti definisani u okviru API pregledaca veba. (`Window`, `Navigator`,
   `Document`)
4. Objekti koji su deo DOM, definisani W3C standardom. Ovi objekti omogucavaju
   JavaScript manipulaciju nad CSSom, i laksi razvod DHTMLa.
* Objekti su kompozitivni tipovi podataka, tj objedinjuju vise vrednosti.
* Objekat je neuredjeni skup *svojstva* od kojih svako ima ime i vrednost
* Objekat se definise unutar `{ }` tako sto se navode svojstva, i to
  `ime: vrednost`, izmedju svojstava se koristi `,`

### Osobine objekata

* Ponasaju se kao promenljive, a mogu da budu bilo koji tip: primitivni, 
  objektni, pa cak i funkcije.
* Pristupanje atributa: `imeObjekta.imeAtributa`
  * Alternativno moze: `imeObjekta["imeAtributa"]`
* Moguce je brisanje svojstva pomocu operatora `delete`.
* Provera da li postoji neki atribut u objektu se koristi operatorom `in`.
* Operator `in` moze da se se korisit i u `for-in` za nabrajanje imena     
  svojstava.

### Metodi kod objekata

* Metodi su osobine koje referisu na vrednost neke funkcije.
* Kljucna rec `this` referise na objekat iz kog se poziva funkcija

## Nizovi

* Niz je uredjeni skup vrednosti. Te vrednosti se nazivaju elementi niza.
* Svaki element ima svoju poziciju tj *index*.
* Niz mozemo posmatrati kao objekat u kome su imena svojstava indeksi, a
  pristup vrednostima dobijamo pomocu tih indeksa
* Deklaracija niza se realizuje tako sto se unutar uglastih zagrade nabroje
  elementi razdvojeni zarezom `[2, 3, 5.2, .2, false, {ime: 'Pera'}]`
* Za rad sa njima koriste se petlje `while`, `do-while`, i `for`
  * Postoje posebne petlje: `for-of` i `for-in`
  * One prolaze kroz vrednosti elemenata niza i kroz indekse niza, respektivno.

### Metodi nad nizovima

* Metodi su osobine koje referisu na vrednosti-funkcije

### Nizovi i objekti

### Niz argumenata pri pozivu funkcije

## Niske

### Metodi nad niskama

* `slice()`, `indexOf()`, `trim()`, `charAt()`

# Funkcije viseg reda

## Funkcije kao argumenti funkcija

* Povratni poziv (callback) omogucava da se funkcija prosledi kao parametar,
  da bi se kasnije pozivala po potrebi.
```
function zaSvaki (niz, akcija) {
    for (let x of niz) {
        akcija(x)
    }
}

prikaziNaKonzolu = (x) >= console.log(x)
niz = [1, 2, 3, 4, 5]

zaSvaki(niz, prikaziNaKonzolu)

niz.forEach(x => console.log(x))
```

## Mapiranje i redukcija pomocu funkcija viseg reda

```
function filter(array, test) {
    let res = []
    for (let i = 0; i < array.length; i++) {
        if (test(array[i])) {
            res.push(array[i])
        }
    }
    return res
}

function map(array, transform) {
    let mapped = []
    for (var i = 0; i < array.length; i++) {
        mapped.push(transform(array[i]))
    }
    return mapped
}

function reduce(array, combine, start) {
    let current = start
    for (let i = 0; i < array.length; i++) {
        current = combine(current, array[i])
    }
    return current
}

recude(niz, (a, b) => a + b; 0) // suma svih elemenata niza
```

## Pretvaranje iterabilnog objekta u niz

* Metodom `form()` iz `Array` moguce je kreirati niz od objekta koji ima
  strukturu koja podseca na niz.
* Prvi argument funkcije je iterabilni objekat, a drugi moze biti gradjnin
  prvog reda, koji ce tada biti primenjen na svaki od elemenata.

## Povezivanje funkcija pri pozivu

* Kako su funkcije gradjani prvog reda nad njima se mogu primenjivati sledece
  ugradjene metode
  1. `call()` Odredjuje u izabranoj funkciji zeljeno znacenje kljucne reci
     `this`, i odmah poziva funkciju. Prvi argument definise objekat na koji
     ce `this` pokazivati dok se ostali argumenti prosledjuju funkciji nad
     kojom se poziva
  2. `apply()` Slicno kao `call()` sem sto se ostali argumenti funkcije 
     prosledjuju kao niz argumenata.
  3. `bind()` Prima jedan argument a to je objekat na koji ce referisati 
     promenljiva `this`. Vraca funkciju koja se moze pozivati, sa istim
     argumentima kao i funkcija nad kojoj je `bind()` pozvana, dok je 
     umesto `this` sada prosledjeni objekat.
* Postupak odredjivanja znacenja `this` je sledeci:
  1. Proverava se da li je to konstruktorska funkcija pozvana sa operatorom
     `new()`. Ako jesto onda `this` pokazuje na primerak funkcije koji
     se kreira
  2. Potom se proverava da li je to funkcija koja je pozvana sa `call()`, ili
     `apply()` (ili je pre toga izvrseno povezivanje sa `bind()`). Ako jeste
     onda `this` referise na odgovarajuci prvi argument prilikom poziva
     ovih funkcija
  3. Potom se proverava da li je ta funkcija metoda nekog objekta. Ako jeste
     onda `this` referise na odgovarajuci objekat nad kojim se poziva metoda.
  4. Ako nije ni jedno od prethodna 3 onda `this` referise na globlani objekat.
     
# Napredni objekti

## Prototip

* *Prototipsko nasledjivanje* je vrsta nasledjivanja gde objekat nasledjuje
  svojstva direktno od drugog objekta.
* Svaki objekat ima svoj prototipski objekat kojeg nasledjuje.
* Lanac nasledjivanja se zavrsava sa `Object.prototype` objektom koji
  je na vrhu hijerarhije.
* Pri trazenju neke osobine ili metode, prvo se proverava da li je onda
  definisana u okviru tog objekta, ako nije onda se proverava njegov roditelj,
  ako pak ni ti ne nadje, onda se proverava roditelj njegovog roditelja, itd.
  sve dok se ne dodje do `Object.prototype` objekta, i ako u njemu ne nadje
  trazenu osboninu onda se vrati `undefined`.
* Ovaj pristup donosi:
  * Smanjuje se memorija koju zauzima svai novi objekat.
  * Objekat nasledjuje svojstva cak i kada se dodaju njegovom prototipu
    nakon sto se objekat napravi.
* Osobine svakog objekta:
  * `prototype` referenca na svoj prototip
  * `constructor` referenca na funkciju konstruktor
  * `valueOf()`, `hasOwnProperty(prop)`, `isPrototypeOf(obj)`,   
    `propertyIsEnumerable(prop)`, `toString()`, toLocaleString()`

## Kreiranje objekata i prototipova

```
let prototipZeca = {
    tip: "непознат",

    govori: function (tekst) {
        console.log("Овај зец " + this.tip + " каже '" +
            tekst + "'");
    }
    let zec = Object.create(prototipZeca);
    zec.govori("Ко сам ја?");
};

let zec = Object.create(prototipZeca)
```

## Konstruktori i prototipovi

* Ako se funkcija pozove sa koriscenjem rezervisane rec `new`, tada se taj
  poziv kreira kao poziv konstruktora, tj. tako pozvana funkcija jeste 
  funkcija-konstruktor.
* Kada se objekat kreirak koriscenjem `new`, tada se kaze da je taj objekat
  primerak svog konstruktora
```
function Zec(tip = "непознат") {
    this.tip = tip;

    this.govori = function (tekst) {
        console.log("Овај зец " + this.tip + " каже '" +
            tekst + "'");
    }
}

let zec = new Zec();
zec.govori("Ко сам ја?");
```
* Dodavanje nove osobine na objekat, nece dodati tu osobinu na njegov
  prototip, vec samo top objektu, Ako ta osobina postoji u prototipu ona ce 
  biti pregazena.
* Konstruktori sadrze osobinu `prototype` koja ce podrazumevano sadrzati
  prazan objekat izveden iz `Object.prototype`.
* Funkcije i metodi se cesto dizajniraju tako da ne menjaju svojstva, vec
  da vracaju novi objekat.

### Prototipovi za predefinisane tipove

* Kada listamo osobine u `for-in` ciklusu onda prolazimo i kroz osobine koje
  su definisane u prototipu nekog objekta.
* Pa koriscenjem reci `in` nije moguce utvrditi da li je ta osobina posebna
  za taj objekat ili je nasledjena od nekog njegovog roditelja.
  * To resavamo pomocu metode `hasOwnProperty(prop)`.

### Prototipsko nasledjivanje

### Prototipsko nasledjivanje za predefinisane tipove

## Klase

```
class Tacka {
    constructor(x = 0, y = 0) {
        this.x = x;
        this.y = y;
    }

    prikazi() {
        console.log(`(${this.x},${this.y})`);
    }

    translacija(xV, yV) {
        return new Tacka(this.x + xV, this.y + yV);
    }

    centralnaSimetrija(xC, yC) {
        return this.translacija(2 * (xC - this.x), 2 * (yC - this.y));
    }
}
```
* Mnogi objektno orijentisani jezici podrazumevaju mogucnost da se neko
  svojstvo ne vidi van klase, tj. da nije moguce pristupiti mu sem ako nismo
  mu ne pristupa neki metod unutar klase.
  * JavaScript ne podrzava ovo, ali moguce je zatvorenjem za funkcije
    postici isto.
```
class Tacka {
  constructor(x = 0, y = 0) {
      this.getX = function() {return x;}
      this.getY = function() {return y;}
  }

  prikazi() {
      console.log(`(${this.getX()},${this.getY()})`);
  }

  translacija(xV, yV) {
      return new Tacka(this.getX() + xV, this.getY() + yV);
  }

  centralnaSimetrija(xC, yC) {
      return this.translacija(2 * (xC - this.getX()), 2 * (yC - this.getY()));
  }
}
```
* Naravno moguce je i nasledjivanje preko klasa i to sa kljucnom reci `extends`
  * Slicno kao i u Javi.

## Metodi za postavljanje i citanje osobina

* Metodi za citanje (getters) i metodi za postavljanje (setters) osobina
  su funkcije koje sluze za napredno definisanje osobina.
* Metod za citanje uvek vraca neko svojstvo pomocu `return` naredbe.
* Slicno tome, metod za postavljanje je funkcija koja se poziva kada se zadaje
  vrednost nekom svojstvu.

# Asinhroni JavaScript

## Tipicni modeli izvrsavanja programa

* sinhroni: program se izvrsava sekvencijalno
* visenitni: vise niti se izvrsava uporedno
* asinhroni: program se izvrsava kada postane moguce da se izvrsi

### Sinhroni model programiranja

* Zadaci se izvrsavaju sekvencijalno, jedan po jedan, tek kada se zavrsi
  prethodni, pocinje sledeci.
* Ako se desi da je sledeca naredba ceka na neki resurs, onda se ceo program
  zaustavlja sve dok ne dobije taj resurs. Ovo ocigledno pravi problem.
* Slicno tako moze da se desi da neka naredba ceka na odgovor korisnika.

### Visenitni model programiranja

* Svaki zadatak se podeli na programske niti. Nitima obicno upravlja 
  operativni sistem i one mogu da se izvrsavaju uporedno na drugim 
  jezgrima procesora.
* Kompleksan je za implementiranje.

### Asinhroni model programiranja

* Asihroni model ima jednu nit, unutar koje se zadaci preplicu.
* Kada se zavrsi neki zadatak, mozemo biti sigurni da se samo taj zadatak
  zavrsio. 
* Asinhroni model je dobar u svim blokirajucim situacijama.

## Asinhrono programiranje u JavaScriptu

* Dobro je zbog cekanja odgovora sa servera, gde ne moramo da blokiramo 
  ceo sistem ako ne dobijemo povratnu informaciju.

### JavaScript okruzenje i asinhrono programiranje

* Realizuje se tako sto se naredve izvrsavaju jedna za drugom.
* Ako neke naredbe ne treba odmah izvrsiti one idu na red za cekanje.
  * Kada budu spremne prebacuju se na red zadataka.
* JavaScript ovo realizuje pomocu povrathnog poziva (callback function)

### Asinhrono programiranje i povratni pozivi

```
let povratniPoziv = () => {
  console.log('Ziv sam!')
}

console.log('Pokrenuto...')
setTimeout(povratniPoziv, 2000)
console.log('Zavrsava...')
```
1. Na stek ide: `console.log('Pokrenuto...')`, i izvrsava se
2. Poziva se `setTimeout`, te ona ide na stek i izvrsava se
3. `setTimeout` se sklanja sa steka, a njena funkcija povratnog poziva
   na koju referise `povratniPoziv` se prebacuje na red povratnih poziva
   na cekanju i ukljucuje casovnik koji broji `2000`ms.
4. Postavlja se na stek `console.log('Zavrsava...')`, i izvrsava se
5. Dok se izvrsava ostali deo programa, a po isteku od `2000`ms funkcija
   povratnog poziva se prebacuje u red zadataka.
6. Kada dodje na red `povratniPoziv`, ona se prebacuje na stek i izvrsava.
7. Kada se izvrsi onda se sklanja sa steka.
* Da bi se ovo primenilo mora postojati mehanizam za sinhronizaciju, tj.
  obezbedjivanje cekanja tamo gde je to neophodno.
  * Ako neka funkcija mora uvek da se izvrsi posle neke druge funkcije,
    onda se ta funkcija postavlja kao povratni poziv kod te druge funkcije.

### Asihrono programiranje i obecanja

* Izraz sa ugnjezdenim funkcijamo povratnih poziva se naziva pakao povratnih
  poziva ili piramida propasti.
* Sa standardom ES2015 imamo novu konstrukciju koja se naziva obecanje     
  (promise), koja obezbedjuje bolji i pregledniji nacin za njihovo    
  organizovanje.
* Obecanje je objekat u kome se cuvaju rezultati asihrone funkcije sve dok
  traje izvrsavanje asihrone operacije.
* Precizno, obecanje je sinhrono vracen objekat pri izvrsenju asinhrone
  operacije, koji predstavlja privremenu zamenu za moguce rezultate te
  asihrone opracije. Obecava da ce dostaviti tu vrednost u nekom trenutku
  u buducnosti.
* Asihrona funkcija moze imaati dva moguca krajnja rezultata, a to su
  uspesno izvrsena operacija ili neuspesno izvrsena operacija.
* Obecanje moze nalaziti u jednom od tri stanja:
  1. Na cekanju (pending) - kada se asihrona radnja jos uvek izvrsava
  2. Ispunjeno (fulfill) - kada se asihrona radnja zavrsila uspsno
  3. Odbijeno (reject) - kada se asihrona radnja nauspesno zavrsila
```
function asinhronaFunkcija() {
    return new Promise(function (resolve, reject) {
            //...kod za asinhronu operaciju...

            if (uspešna operacija) {
               resolve(result_value);
            } else {
               reject(error);
            }
        }
    );
}
```
* U zavisnosti od uspesnosti funkcija poziva jedno od dve funkcije:
  1. Funkcija za razresavanje (resolve) se poziva u delu koda koji obradjuje
     uspesno izvrsenu asihronu operaciju, njen parametar je vrednost 
     rezultujuceh podatka.
  2. Funkcija za odbijanje (reject) se poziva u delu koda koji obradjuje
     slucaj kada se pojavi problem sa izvrsavanje asihrone operacije.
     Parametar ove funkcije je razlog neuspeha izvrsavanja asihrone operacije.

### Asihrono programiranje i narede async i await

* Obecanje moze da se zakomplikuje pa je sa standardom ES2017 stigla i nova
  sintaksa pomocu async/await, koja olaksava rad sa obecanjima i omogucava
  jednostavnije predstavljanje serija asihronih obecanja.
* Citljivije prikazivanje visestruke mogucnosti zavisne asihrone radnje.
* Asinhrona funkcija se obelezava sa kljucnom reci `async` i ona izvrsava
  asinhroni kod.
  1. Automatski konvertuje regularnu funkciju u obecanje
  2. Sve sto je vraceno pomocu `return` biva prosledjeno funkciji za
     razresavanja.
  3. Asihrona funkcija omogucava koriscenje `await` operatora.
* Operator `await` moze da se koristi samo unutar asihrone funkcije, gde
  pauzira njeno izvrsavanje. tj. ona zaustavlja izvrsavanje funkcije sve
  dok se ne dobije vrednost operacije nad kojom je postavljen `await`.

# Rukovanje greskama

## Hvatanje gresaka u programskom kodu

* Kada se ukljuci strikt mod, okruzenje kontrolise da li su deklarisane
  promenljive u kodu.
```
function gdeLiJeProblem() {
  "use strict";
  for (brojac = 0; brojac < 5; brojac++)
    console.log("Срећа, срећа, радост!");
}

gdeLiJeProblem();



"use strict";
function Osoba(ime) {
  this.ime = ime;
}

// Greska, zaboravljen 'new' ?
let mikiMaus = Osoba("Мики Маус");
```

## Reagovanje na greske

* Moze doci do greske prilikom izvrsavanja funkcije.
* Kada dodje do greske mozemo to da signaliziramo tako sto vratimo rezultat
  koji ce da opisuje gresku
* Uobicajno signaliziramo gresku pereko `null` ili `undefined`
* Ovaj pristup ima sledece negativne osobine:
  1. Sta se desava ako funkcija vraca sve moguce vrednosti iz domena?
  2. Moze biti tesko za citanje

## Izuzeci

* Omogucava da funkcija izbaci izuzetak kada dodje do greske, koji ukazuje
  da je doslo do problema.
* Zaustavlja dalji rad funkcije, i sa steka skida sve funkcije u lancu koje
  pozivaju jedna drugu.
  * Ovo se naziva odmotavanje steka poziva.
* Izuzetak moze da se uhvati i da na taj nacin prekinje spustanje nanize.

### Izbacivanje izuzetka

* Koristimo kljucnu rec `throw`

### Hvatanje izuzetaka

* Koristi se `try-catch` blok.

### Finalno pospremanje kod izuzetaka

* Da li se prilikom odmotavanja moze doci u situaciju da konteksti funkcija 
  koji se izvrsavaju budu izgubljeni.

### Selektivno hvatanje izuzetaka

* Ne postoji podrska za selektovano hvatanje izuzetaka, ili ce se uhvatiti
  svi izuzeci, ili se nece uhvatiti nijedan.
* Pozeljno je da se u takvim situacijama definisu novi tipovi izuzetaka i da
  se prilikom hvatanja oni identifikuju koriscenjem `instanceof`.

## Tvrdnje

* Tvrdnje su alat za osnovnu kontrolu programa, koji olaksava pronalazak 
  bagova. 
* Tvrdnje predstavljaju nacin da se obezbedi da greske dovode do prekida   
  izvrsavanja tamo gde je nastala greska, kako bi se sprecilo da ta greska
  u tisini poizvede besmislenu brednost, koja bi mogla da izazove problem
  u nekom drugom delu sistema.
* Sintaksa je `assert` pa uslov koji mora da vazi kako bi se program
  dalje nastavio

# Moduli

* Zasniva se na razbijanju jedne velike aplikacije na manje, nezavisne delove,
  koji se nazivaju moduli.
* Cilj modularnosti jeste da se smanji kompleksnost prema principu podeli
  pa vladaj.
* Najznacajnije prednosti modularnog programiranja:
  * preglednija i razumljivija aplikacija
  * lakse kontrolisanje opsega definisanosti promenljivih
  * sprecavanje da globalni opseg definisanosti bude zagadjen
  * ponovna upotrebljivost koda
  * mogucnost rada na istim projektu vise razlicitih timova ili programera
    koji rade odvojene manje zadatke
  * lakse debagiranje
* Modularno programiranje omogucavaju:
  * nativna ES5 sintaksa
  * ES5 sintaksa sa spoljnim bibliotekama
  * Sintaksa RS6 modele
* Za ucitavanje modela koriste se alati za ucitavanje modela (module loader)
  i za uvezivanje se koristi (module bundler)

## Nativni ES5 moduli

* Koriste se obrasci (pattern) koji imaju slicnosti sa modularnim 
  pogramiranjem, ali nemaju bas sve karakteristike.
* Koriscenjem funkcijskih izraza koji se odmah izvrsavaju ili koriscenjem 
  konstruktora.
* Ono sto treba da bude dostupno spoljasnosti se vraca iz funkcije pomocu
  kljucne reci `return`.
* Mene:
  * zagadjivanje globalnog opsega imena nazivima modula.
  * potreba za rucnim odredjivanjem redosleda ucitavanja modula
  * nemogucnost asihronih ucitavanja modula

### Moduli preko funkcijskih izraza koji se odmah izvrsavaju

* Funkcijski izrazi koji se odmah izvrsavaju (Immediately-Invoked Function
  Expression - IIFE), su funkcijski izrazi koji se izvrsavaju odmah nakon
  stvaranja.
* Sintaksa: `( function(){blok} )()`
* Sve unutar postace lokalna promenljiva a ne globalna, takodje kako
  nismo deklarisali ime funkcije ono nece biti vidljivo globalno

### Moduli preko konstruktora

* Kako se radi o konstruktoru, naziv promenljive kojoj se dodeljuje funkcija
  treba da pocinje velikim slovom
* Funkcijski izraz koji se odmah izvrsava se transformise u obicnu funkciju,
  brisanjem zagrada koje odmah pozivaju funkciju, jer se standardna 
  konstruktorska funkcija poziva sa rezervisanom reci `new`.
* Unutar modula koji poziva metodu iz drugog modula potrebno je instancirati
  novi objekat da bi bila dostupna njegova metoda.

## ES5 moduli preko spoljnih biblioteka

* Dobija nove mogucnosti:
  * Asinhrona definicija modula (AMD)
  * CommonJS moduli
  * Univerzalna definicija modula (UMD)

### Asinhrona definicija modula

* Osnovna sintaksa je funkcija `define()`, koja preko prosledjenih 
  argumenata definise sam modul i zavisnosti od drugih modula.
  * `id` niska koja predstavlja naziv modula
  * `dependencies` - niz niski sa nazivom potrebnih modula ili relevantnih
    putanja do svih modula koji su potrebni za uspesan rad datog modula.
    Redosled je vazan.
  * `factory` - funkcija povratnog poziva koja kreira objekta-modul.
* Koristi se `require.js` za ucitavanje modula
  * funkcija `requirejs()` se koristi za izvrsavanje programskog koda koji
    zavisi od modula
* Dobijamo:
  * menadzment modula u sklopu alata za ucitavanje umesto rucnog odredjivanja
    redosleda ucitavanja modula.
  * globalni prostor je zagadjen samo sa jednim imenom `require` umesto
    sa svim nezivima modula
* Mane:
  * kod funkcije `define()` lista zavisnosti u nizu mora da se slaze sa 
    listom argumenata prosledjenih funkciji
  * sistaksa zahteva da je ceo kod obavijen sa `define()` funkcijom
  * ucitavanje velikog broja malih datoteka moze da izazove gubitak 
    performansi

### CommonJS moduli

* Izvoz:
  1. dodeljivanjem svake metode pojedinacno objektu `module.export`
  2. dodeljivanjem objekta sa zeljenim metodama objektu `module.export`
* Uvoz:
  * Koristi se funkcija `require()`, koja prima relativnu putanju do modula
    koji zahteva, a kao rezultat vraca referencu na zahtevani modul.
* Mane:
  * sinhroni rad nije bas najbolji za pregledac i u tom kontekstu je obavezno
    koriscenje alata za uvezivanje
  * svaki modul je potrebno smestiti u jednu odvojen datoteku
  * ne podrzava cilicne zavisnosti
  * Ima dinamicku struktura modula

## ES6 moduli

* Ova podrska dolazi ugradjena u sam jezik.
* Podrzava module koji se smestaju u datoteke
* Moduli su unikatni, ili jednistveni primerci, ili singlotni
* ES6 moduli mogu da rade i sinhrono i asinhrono
* Podrzana je ciklicna zavisnost modula
* Sintaksa je jos kompaktnije od CommonJS
* Standardni izvoz: `export`
* Podrazumevani izvoz: `export default`
* Uvoz modula: `import-from`
* Karakteristike uvoza
  * deklaracija promenljive ili funkcije se u fazi prevodjena dize na pocetak
    oblasti definisanosti
  * svi uvezeni elementi su nepromenjivi iz modula koji vrsi uvoz.
  * nije dozvoljeno koriscenje promenjivih u naredbi `import`.
  * Uslovno ucitavanje modula samo sa ES6 sitnaksom nije moguce

## Alati za ucitavanje i za uvezivanje modula

* Problem nastaje sa velikim brojem modula i njihove medjusobne zavisnosti
  (dependinces). Zbog toga se koriste alati za ucitavanje i za uvezivanje
  modula su neophodna podrska programeru za jednostavniji i efikasniji rad 
  sa modulima.

### Alati za ucitavanje modula

* RequireJS
* SystemJS

### Alati za uvezivanje modula

* Browserify
* Webpack

# JavaScript programiranje koriscenjem okruzenja node

## Okruzenje node

* Viseplatformsko radno okruzenje koje se bazira na Google Chrome V8 masini.

### Karakteristike okruzenja node

* U *potpunosti je JavaScript*, koji donosi programiranje na serverskoj strani
* *Modularnost*
* Instalacija modula pomocu *npm*
* Podrzani su *dogadjaji*.
* Princim rada:
  1. Primi zahtev od strane klijenta, taj zahtev se smesta u red dogadjaja.
  2. Ako je zahtev nebolokirajuci, okruzenje ce jednostavno obraditi zahtev.
  3. Ako je zahtev blokirajuci, on se dodaje skupu niti (threading pool)
     koja realizuje blokirajuca operacija, kao sto je prikazano na slici 
     koja sledi.
  4. Kada je blokirajuca operacija zavrsena, radna nit (worker thread) prima
     odgovor i salje ga petlji za dogadjaje, koja taj odgovor salje klijentu.

### Menadzer paketa npm

* Moduli se mogu posmatrati kao neka vrsta JavaScrip biblioteka, a zapravo
  predstavljaju skup razvijenih funkcija.
* Postoje ugradjeni moduli, a i oni koji se instaliraju po potrebi
* To je omoguceno preko npm
* Instalirani moduli se dodaju u listu zavisnosti `package.json`

## Dogadjaji kod okruzenja node

* Koriste se `async` funkcije u ciljlu obezbedjenja konkurentnosti.
* Koristi obrazac dizajna posmatrac (observer pattern).
  * Jedna nit node aplikacije se vrti u okviru petlje za dogadjaje sve dok
    se zadatak ne zavrsi, a potom ispaljuje odgovarajuci dogadjaj kojim se
    signalizira da treba da bude izvrsena funkcija koja osluskuje taj 
    dogadjaj.

### Programiranje upravljano dogadjajima

* Postoji jedna glavna petlja u kojoj se osluskuju dogadjaji i potom
  pokrecu funkcije povratnih poziva kada se detektuju dogadjaji
  odgovarajuceg tipa.
* Kod dogadjaja funkcije koje osluskuju dogadjaje se ponasaju kao posmatraci:
  kada dogadjaj bude ispaljen, pocinje sa izvrsavanje osluskivaca dogadjaja.
* Omogucuje se preko module `event` kroz klasu `EventEmitter`.

### Klasa EventEmitter

* Obezbedjuje da objekat tipa `EventEmitter` sadrze osobine kao sto su
  `on` i `emit`. 
  * `on` se koristi radi vezivanja funkcije za dati dogadjaj
  * `emit` sluzi za ispaljivanje dogadjaja
* `addListener(dogadjaj, osluskivac)`
* `on(dogadjaj, osluskivac)`
* `once(dogadjaj, osluskivac)`
* `removeListener(dogadjaj, osluskivac)`
* `removeAllListener([dogadjaj])
* `setMaxListeners(n)`
* `listeners(dogadjaj)`
* `emit(dogadjaj, [arg1], [arg2], ...)
* Nad dogadjajima se mogu praviti dogadjaji, tj. dva tipa dogadjaja:
  1. `newListener` - emituje se svaki put kada se doda osluskivac za neki
     dogadjaj.
  2. `removeListener` - emituje se svaki put kada osluskivac bude uklonjen.

## Rad sa datotekama

### Direktan rad sa datotekama

```
let fs = require('fs')

fs.readFile('test.txt', 'utf-8' (err, data) => {
    if (err) {
        console.log(err)
    }
    console.log(data)
})
```

### Rad sa datotekama preko tokova

```
let fs = require('fs');

console.log('\n');

let tokZaCitanje = fs.createReadStream('lorem.txt');
tokZaCitanje.setEncoding('utf8');
tokZaCitanje.once('data',
    (datacoming) => console.log(datacoming));

let tokZaUpis = fs.createWriteStream('copyl.txt');
tokZaUpis.write('Поздрав за слушапоце курса УВИТ!');
```

### Dogadjaji i tokovi podataka

```
let fs = require('fs');

let tokZaCitanje = fs.createReadStream('lorem.txt');
tokZaCitanje.setEncoding('utf8');

let brojac = 0;
tokZaCitanje.addListener('data', brojiCitanja);
tokZaCitanje.addListener('data', prikazujeCitanja);

function brojiCitanja(prispeliPodaci) {
    brojac = brojac + 1;
    console.log("Citanje broj: " + brojac);
}

function prikazujeCitanja(prispeliPodaci) {
    console.log('Duzina prispelih podataka: ' + prispeliPodaci.length);
}

tokZaCitanje.addListener('end',
    function () {
        console.log("---\nUkupno citanja: " + brojac);
    });
```

# JavaScript serversko programiranje koriscenjem okruzenja node

## Mrezne aplikacije 

### TCP aplikacije

```
let net = require('net');

let server = net.createServer(
    (soket) => {
        soket.write(`Pozdrav od servera\n`);
        soket.pipe(soket);
    });

adresa = '127.0.0.1';
port = 1337;
server.listen(port, adresa);
console.log(`Server slusa na adresi ${adresa}, port ${port} `);
```

### UDP aplikacije

## Obrada veb formulara

### Metod GET

### Metod POST
